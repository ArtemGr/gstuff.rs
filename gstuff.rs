#![allow(unknown_lints, uncommon_codepoints)]
#![allow(unused_imports)]

#![cfg_attr(feature = "nightly", feature(test))]

#![cfg_attr(feature = "re", feature(try_trait_v2))]
#![cfg_attr(feature = "re", feature(never_type))]

#[macro_use] extern crate lazy_static;
extern crate libc;
#[cfg(feature = "crossterm")] extern crate crossterm;

//use std::fmt;
//use std::marker::PhantomData;
use core::any::Any;
use core::arch::asm;
use core::str::{from_utf8_unchecked}; //, FromStr};
use core::sync::atomic::{AtomicUsize, Ordering};
use std::fs;
use std::io::{self, Read};
use std::os::raw::c_int;
use std::path::Path;
use std::process::{Command, Stdio};
use std::sync::Mutex;
use std::time::{Duration, SystemTime, UNIX_EPOCH};
#[cfg(test)] use std::thread::sleep;

/// Shortcut to path->filename conversion.
///
/// Returns the unchanged `path` if there is a character encoding error or something.
pub fn filename<'a> (path: &'a str) -> &'a str {
  // NB: `Path::new (path) .file_name()` only works for file separators of the current operating system,
  // whereas the error trace might be coming from another operating system.
  // In particular, I see `file_name` failing with WASM.

  let name = match path.rfind (|ch| ch == '/' || ch == '\\') {
    Some (ofs) => &path[ofs+1..],
    None => path};

  if name.ends_with (".rs") {&name[0 .. name.len() - 3]} else {name}}

// A trick to use the `try_s` macro from both the outside and inside of the crate.
//mod gstuff {pub fn filename<'a> (path: &'a str) -> &'a str {::filename (path)}}

/// Returns on error, converting the `Err` value to `String` and prepending the current location.
///
/// cf. http://www.reddit.com/r/rust/comments/29wwzw/error_handling_and_result_types/cipcm9a
#[macro_export] macro_rules! try_s {
  ($e: expr) => {match $e {
    Ok (ok) => ok,
    Err (err) => {return Err (format! ("{}:{}] {}", $crate::filename (file!()), line!(), err));}}}}

/// Returns on error, prepending the current location to a stringified error, then passing the string to `From::from`.
#[macro_export] macro_rules! try_f {
   ($e: expr) => {match $e {
     Ok (ok) => ok,
     Err (err) => {return Err (From::from (format! ("{}:{}] {}", $crate::filename (file!()), line!(), err)));}}}}

/// Like `try_s`, but takes a reference.
#[macro_export] macro_rules! try_sp {
  ($e: expr) => {match $e {&Ok (ref ok) => ok,
    &Err (ref err) => {return Err (From::from (format! ("{}:{}] {:?}", $crate::filename (file!()), line!(), err)));}}}}

/// Lifts an error into a boxed future. `Box<Future<Item=_, Error=_>>`.
///
/// For example:
///
///     Box::new (PGA.execute (select) .and_then (move |pr| -> Box<Future<Item=Vec<PgResult>, Error=PgFutureErr> + Send> {
///       let day = try_fu! (pr[0].row (0) .col_str (0));
///       let json = try_fu! (pr[0].row (0) .col_json (1, "stats"));
///       let mut stats: S = try_fu! (json::from_value (json));
///       ...
///       Box::new (PGA.execute (update))
///     }))
#[macro_export] macro_rules! try_fu {
  ($e: expr) => {match $e {
    Ok (ok) => ok,
    Err (err) => {return Box::new (futures01::future::err (From::from (err)))}}}}

/// Lifts an error into a boxed future. `Box<Future<Item=_, Error=String>>`.
///
///     fn foo() -> Box<Future<Item=u32, Error=String>> {
///       try_fus! (bar());
///       let another_future = try_fus! (whatever());
///       Box::new (another_future.then (move |something| Ok (123)))
///     }
#[macro_export] macro_rules! try_fus {
  ($e: expr) => {match $e {
    Ok (ok) => ok,
    Err (err) => {return Box::new (futures01::future::err (ERRL! ("{}", err)))}}}}

/// Prepends file name and line number to the given message.
#[macro_export] macro_rules! ERRL {
  ($format: expr, $($args: tt)+) => {format! (concat! ("{}:{}] ", $format), $crate::filename (file!()), line!(), $($args)+)};
  ($format: expr) => {format! (concat! ("{}:{}] ", $format), $crate::filename (file!()), line!())}}

/// Returns a `Err(String)`, prepending the current location (file name and line number) to the string.
///
/// Examples: `ERR! ("too bad")`; `ERR! ("{}", foo)`;
#[macro_export] macro_rules! ERR {
  ($format: expr, $($args: tt)+) => {Err (ERRL! ($format, $($args)+))};
  ($format: expr) => {Err (ERRL! ($format))}}

#[cfg(feature = "base62")]
pub mod base62;

#[cfg(feature = "base62j")]
pub mod base62j;

#[cfg(all(feature = "base91", feature = "nightly"))]
pub mod base91;

#[cfg(feature = "re")]
pub mod re;

#[cfg(feature = "lines")]
pub mod lines;

// --- status line -------

#[cfg(all(feature = "crossterm", not(target_arch = "wasm32")))]
fn isatty (fd: c_int) -> c_int {unsafe {libc::isatty (fd)}}

#[cfg(all(feature = "crossterm", target_arch = "wasm32"))]
fn isatty (_fd: c_int) -> c_int {0}

#[cfg(feature = "crossterm")]
lazy_static! {
  static ref STATUS_LINE: Mutex<String> = Mutex::new (String::new());
  /// True if the standard output is a terminal.
  pub static ref ISATTY: bool = isatty (1) != 0;
  pub static ref STATUS_LINE_LM: AtomicUsize = AtomicUsize::new (0);}

/// The time of the last status line update, in milliseconds.  
/// Tracked in order to help the calling code with implementing debounce strategies
/// (for sending each and every update to the terminal might be a bottleneck,
/// plus it might flicker
/// and might be changing too fast for a user to register the content).
#[cfg(feature = "crossterm")]
pub fn status_line_lm() -> u64 {STATUS_LINE_LM.load (Ordering::Relaxed) as u64}

/// Reset `status_line_lm` value to 0.  
/// Useful for triggering a status line flush in a code that uses a delta from `status_line_lm` to debounce.
#[cfg(feature = "crossterm")]
pub fn status_line_lm0() {STATUS_LINE_LM.store (0, Ordering::Relaxed)}

/// Clear the rest of the line.
#[cfg(feature = "crossterm")]
fn delete_line (stdout: &mut io::Stdout) {
  use crossterm::{terminal, QueueableCommand};

  let _ = stdout.queue (terminal::Clear (terminal::ClearType::UntilNewLine));}
// ^^ Checking whether crossterm will do better than term

  // NB: term's `delete_line` is really screwed.
  // Sometimes it doesn't work. And when it does, it does it wrong.
  // Documentation says it "Deletes the text from the cursor location to the end of the line"
  // but when it works it clears the *entire* line instead.
  // I should probably find something better than term, unless it's `delete_line` is fixed first.

//  if cfg! (windows) {
//  } else {
//    let _ = stdout.write (b"\x1B[K");}}  // EL0. Clear right.

/// Clears the line to the right, prints the given text, moves the caret all the way to the left.
///
/// Will only work if the terminal `isatty`.
///
/// Repeating this call will keep updating the same line (effectively a status line).
///
/// And it's kind of compatible with the normal stdout logging because the latter will overwrite the status line.
///
/// One can also call `status_line_clear()` to clear the line before the normal output comes forth
/// in order to avoid leaving stray characters on the screen.
///
/// Skips spewing the output if the hash of the generated status line is identical to the existing one.
///
/// The function is intended to be used with a macros, for example:
///
///     use gstuff::{status_line, ISATTY};
///     macro_rules! status_line {($($args: tt)+) => {if *ISATTY {
///       status_line (file!(), line!(), fomat! ($($args)+))}}}
#[cfg(all(feature = "crossterm"))]
pub fn status_line (file: &str, line: u32, status: String) {
  use crossterm::{QueueableCommand, cursor};
  use io::{stdout, Write};
  use std::collections::hash_map::DefaultHasher;
  use std::hash::Hasher;

    if let Ok (mut status_line) = STATUS_LINE.lock() {
      let mut stdout = stdout();
      let old_hash = {let mut hasher = DefaultHasher::new(); hasher.write (status_line.as_bytes()); hasher.finish()};
      status_line.clear();
      use std::fmt::Write;
      let _ = write! (&mut *status_line, "{}:{}] {}", filename (file), line, status);
      let new_hash = {let mut hasher = DefaultHasher::new(); hasher.write (status_line.as_bytes()); hasher.finish()};
      if old_hash != new_hash {
        STATUS_LINE_LM.store (now_ms() as usize, Ordering::Relaxed);

        // Try to keep the status line withing the terminal bounds.
        match crossterm::terminal::size() {
          Ok ((w, _)) if status_line.chars().count() >= w as usize => {
            let mut tmp = String::with_capacity (w as usize - 1);
            for ch in status_line.chars().take (w as usize - 1) {tmp.push (ch)}
            let _ = stdout.write (tmp.as_bytes());},
          _ => {let _ = stdout.write (status_line.as_bytes());}};

        delete_line (&mut stdout);
        let _ = stdout.queue (cursor::MoveToColumn (0));
        let _ = stdout.flush();}}}

/// Clears the status line if stdout `isatty` and `status_line` isn't empty.
#[cfg(feature = "crossterm")]
pub fn status_line_clear() {
  use io::{stdout, Write};

  if let Ok (mut status_line) = STATUS_LINE.lock() {
    if *ISATTY && !status_line.is_empty() {
      let mut stdout = stdout();
        STATUS_LINE_LM.store (now_ms() as usize, Ordering::Relaxed);
        status_line.clear();
        delete_line (&mut stdout);
        let _ = stdout.flush();}}}

/// Clear the status line, run the code, then restore the status line.
///
/// Simply runs the `code` if the stdout is not `isatty` or if the status line is empty.
#[cfg(feature = "crossterm")]
pub fn with_status_line (code: &dyn Fn()) {
  use crossterm::{QueueableCommand, cursor};
  use io::{stdout, Write};

  if let Ok (status_line) = STATUS_LINE.lock() {
    if !*ISATTY || status_line.is_empty() {
      code()
    } else {
      let mut stdout = stdout();
      delete_line (&mut stdout);
      let _ = stdout.flush();  // We need to send this EL0 out because the $code might be writing to stderr and thus miss it.
      code();
      // TODO: Should probably use `term_size::dimensions` to limit the status line size, just like in `fn status_line`.
      let _ = stdout.write (status_line.as_bytes());
      let _ = stdout.queue (cursor::MoveToColumn (0));
      let _ = stdout.flush();}}}

#[cfg(feature = "crossterm")]
#[test] fn test_status_line() {
  with_status_line (&|| println! ("hello world"));}

#[cfg(feature = "crossterm")]
pub fn short_log_time (ms: u64)
-> chrono::format::DelayedFormat<chrono::format::strftime::StrftimeItems<'static>> {
  use chrono::TimeZone;
  let time = chrono::Local.timestamp_millis (ms as i64);
  time.format ("%d %H:%M:%S")}

#[cfg(all(feature = "crossterm", feature = "chrono", feature = "fomat-macros"))]
#[macro_export] macro_rules! log {

  (q $command: expr, $($args: tt)+) => {{
    $crate::with_status_line (&|| {
      use crossterm::QueueableCommand;
      use fomat_macros::{wite, fomat};
      let mut stdout = std::io::stdout();
      let _ = stdout.queue ($command);
      let _ = wite! (&mut stdout,
        ($crate::short_log_time ($crate::now_ms())) ' '
        ($crate::filename (file!())) ':' (line!()) "] "
        $($args)+ '\n');
      let _ = stdout.queue (crossterm::style::ResetColor);
      let _ = stdout.flush();})}};

  // https://docs.rs/crossterm/latest/crossterm/style/enum.Color.html
  (c $color: expr, $($args: tt)+) => {
    log! (q crossterm::style::SetForegroundColor ($color), $($args)+)};

  // https://en.wikipedia.org/wiki/ANSI_escape_code#8-bit
  // https://www.ditig.com/256-colors-cheat-sheet
  (a $ansi: expr, $($args: tt)+) => {
    log! (q crossterm::style::SetForegroundColor (
      crossterm::style::Color::AnsiValue ($ansi)), $($args)+)};

  ($($args: tt)+) => {{
    $crate::with_status_line (&|| {
      use fomat_macros::{pintln, fomat};
      pintln! (
        ($crate::short_log_time ($crate::now_ms())) ' '
        ($crate::filename (file!())) ':' (line!()) "] "
        $($args)+);})}};}

#[cfg(all(feature = "crossterm", feature = "chrono", feature = "fomat-macros"))]
#[test] fn test_log() {
  log! ([= 2 + 2])}

/// A helper to build a string on the stack.
///
/// Given an array it makes a writeable cursor available to the passed code block.
///
/// Returns a &str slice pointing at memory between the array start and the cursor.
///
/// Example:
///
///     use std::io::Write;
///     let mut foobar: [u8; 128] = unsafe {std::mem::uninitialized()};
///     let foobar = gstring! (foobar, {
///         write! (foobar, "foo") .expect ("!write");
///         write! (foobar, "bar") .expect ("!write");
///     });
///
/// Alternatives: https://crates.io/crates/stack.
#[macro_export] macro_rules! gstring {($array: ident, $code: block) => {{
  let end = {
    let mut $array = ::std::io::Cursor::new (&mut $array[..]);
    let $array = &mut $array;
    $code;
    $array.position() as usize};
  unsafe {::std::str::from_utf8_unchecked (&$array[0..end])}}}}

/// Fomat into a small string.
/// 
/// Typical imports:
/// 
///     use inlinable_string::{InlinableString, StringExt};
///     use std::fmt::{Write as FmtWrite};
#[cfg(feature = "fomat-macros")]
#[macro_export] macro_rules! ifomat {
  ($($args: tt)+) => ({
    let mut is = InlinableString::new();
    wite! (&mut is, $($args)+) .expect ("!wite");
    is})}

/// Takes a netstring from the front of the slice.
///
/// Returns the unpacked netstring and the remainder of the slice.
///
/// NB: Netstring encoding is not included as a separate function
/// because it is as simple as `write! (&mut buf, "{}:{},", payload.len(), payload);`.
pub fn netstring (at: &[u8]) -> Result<(&[u8], &[u8]), String> {
  let length_end = match at.iter().position (|&ch| ch < b'0' || ch > b'9') {Some (l) if l > 0 => l, _ => return ERR! ("No len.")};
  match at.get (length_end) {Some (&ch) if ch == b':' => (), _ => return ERR! ("No colon.")};
  let length = unsafe {from_utf8_unchecked (&at[0 .. length_end])};
  let length: usize = try_s! (length.parse());
  let bulk_pos = 0 + length_end + 1;
  let bulk_end = bulk_pos + length;
  match at.get (bulk_end) {Some (&ch) if ch == b',' => (), _ => return ERR! ("No comma.")}
  Ok ((&at[bulk_pos .. bulk_end], &at[bulk_end + 1 ..]))}

/// Wraps `gethostname` to fetch the current hostname into a temporary buffer.
#[cfg(unix)]
pub fn with_hostname (visitor: &mut dyn FnMut (&[u8])) -> Result<(), std::io::Error> {
  use libc::{size_t, gethostname};  // http://man7.org/linux/man-pages/man2/gethostname.2.html
  use std::ffi::CStr;

  let mut buf = [0; 128];
  let rc = unsafe {gethostname (buf.as_mut_ptr(), (buf.len() - 1) as size_t)};
  if rc == 0 {
    let cs = unsafe {CStr::from_ptr (buf.as_ptr())};
    Ok (visitor (cs.to_bytes()))
  } else {
    Err (io::Error::last_os_error())}}

#[cfg(unix)] #[test] fn test_hostname() {
  let mut hostname = String::new();
  with_hostname (&mut |bytes| hostname = String::from_utf8_lossy (bytes) .into_owned()) .unwrap();}

/// Read contents of the file into a `Vec`.
///
/// Returns an empty `Vec` if the file is not present under the given path.
pub fn slurp (path: &dyn AsRef<Path>) -> Vec<u8> {
  let mut file = match fs::File::open (path) {
    Ok (f) => f,
    Err (ref err) if err.kind() == io::ErrorKind::NotFound => return Vec::new(),
    Err (err) => panic! ("Can't open {:?}: {}", path.as_ref(), err)};
  let mut buf = Vec::new();
  file.read_to_end (&mut buf) .expect ("!read");
  buf}

/// Runs a command in a shell, returning stderr+stdout on success.
///
/// Sometimes we need something simpler than constructing a Command.
///
/// If the command failed then returns it's stderr
pub fn slurp_prog (command: &str) -> Result<String, String> {
  let output = match Command::new ("dash") .arg ("-c") .arg (command) .output() {
    Ok (output) => output,
    Err (ref err) if err.kind() == io::ErrorKind::NotFound => {  // "dash" was not found, try a different name.
      try_s! (Command::new ("sh") .arg ("-c") .arg (command) .output())},
    Err (err) => return ERR! ("{}", err)};

  let combined_output: String = if output.stderr.is_empty() {
    try_s! (String::from_utf8 (output.stdout))
  } else if output.stdout.is_empty() {
    try_s! (String::from_utf8 (output.stderr))
  } else {
    let mut buf = String::with_capacity (output.stderr.len() + output.stdout.len());
    buf.push_str (try_s! (std::str::from_utf8 (&output.stderr[..])));
    buf.push_str (try_s! (std::str::from_utf8 (&output.stdout[..])));
    buf};

  if output.status.success() {Ok (combined_output)} else {Err (combined_output)}}

#[test] fn test_slurp_prog() {
  if cfg! (windows) {println! ("Skipping as dash might be missing on Windows sometimes"); return}
  let foo = match slurp_prog ("echo foo") {Ok (foo) => foo, Err (err) => panic! ("{}", err)};
  assert_eq! (foo.trim(), "foo");}

/// Run a command, printing it first. Stdout and stderr are forwarded through (`inherit`).
pub fn cmd (cmd: &str) -> Result<(), String> {
  println! ("$ {}", cmd);
  let status = try_s! (Command::new ("dash") .arg ("-c") .arg (cmd) .stdout (Stdio::inherit()) .stderr (Stdio::inherit()) .status());
  if !status.success() {Err (format! ("Command returned an error status: {}", status))} else {Ok(())}}

/// Useful with panic handlers.
/// 
/// For example:
/// 
///     if let Err (err) = catch_unwind (AssertUnwindSafe (move || {
///       let mut core = tokio_core::reactor::Core::new().expect ("!core");
///       loop {core.turn (None)}
///     })) {println! ("CORE panic! {:?}", any_to_str (&*err)); std::process::abort()}
pub fn any_to_str<'a> (message: &'a dyn Any) -> Option<&'a str> {
  if let Some (message) = message.downcast_ref::<&str>() {return Some (message)}
  if let Some (message) = message.downcast_ref::<String>() {return Some (&message[..])}
  return None}

/// Converts the duration into a number of seconds with fractions.
pub fn duration_to_float (duration: Duration) -> f64 {
  duration.as_secs() as f64 + ((duration.subsec_nanos() as f64) / 1000000000.0)}

/// Converts time in milliseconds into a number of seconds with fractions.
pub fn ms2sec (ms: u64) -> f64 {
  (ms / 1000) as f64 + ((ms % 1000) as f64 / 1000.0)}

/// The current number of seconds since UNIX epoch, with fractions.
///
/// cf. http://stackoverflow.com/a/26878367/257568 (C++, Boost).
pub fn now_float() -> f64 {
  let now = SystemTime::now().duration_since (UNIX_EPOCH) .expect ("!duration_since");
  duration_to_float (now)}

#[test] fn test_now_float() {
  let now = SystemTime::now().duration_since (UNIX_EPOCH) .expect ("!duration_since") .as_secs();
  let t1 = now_float();
  assert_eq! (now, t1 as u64);
  sleep (Duration::from_millis (100));
  let t2 = now_float();
  let delta = t2 - t1;
  assert! (delta >= 0.098 && delta <= 0.150, "delta: {}", delta);}

/// Converts the duration into a number of milliseconds.
pub fn duration_to_ms (duration: Duration) -> u64 {
  duration.as_secs() * 1000 + (duration.subsec_nanos() / 1000000) as u64}

/// The current number of milliseconds since UNIX epoch.
pub fn now_ms() -> u64 {
  let now = SystemTime::now().duration_since (UNIX_EPOCH) .expect ("!duration_since");
  duration_to_ms (now)}

#[test] fn test_now_ms() {
  let t1 = now_ms();
  sleep (Duration::from_millis (100));
  let t2 = now_ms();
  let delta = t2 - t1;
  assert! (delta >= 98 && delta <= 150, "delta: {}", delta);}

/// Last-modified of the file in seconds since the UNIX epoch, with fractions.  
/// Returns 0 if the file does not exists.
///
/// A typical use case:
///
///     if (now_float() - try_s! (last_modified_sec (&path)) > 600.) {update (&path)}
pub fn last_modified_sec (path: &dyn AsRef<Path>) -> Result<f64, String> {
  let meta = match path.as_ref().metadata() {
    Ok (m) => m,
    Err (ref err) if err.kind() == std::io::ErrorKind::NotFound => return Ok (0.),
    Err (err) => return ERR! ("{}", err)};
  let lm = try_s! (meta.modified());
  let lm = duration_to_float (try_s! (lm.duration_since (UNIX_EPOCH)));
  Ok (lm)}

// Consider targeting a CPU here.
// https://github.com/rust-lang/rust/issues/44036

/// Time Stamp Counter (number of cycles).
#[cfg(all(feature = "nightly", feature = "rdtsc"))]
pub fn rdtsc() -> u64 {
  // https://stackoverflow.com/a/7617612/257568
  // https://stackoverflow.com/a/48100158/257568
  // https://github.com/Amanieu/rfcs/blob/inline-asm/text/0000-inline-asm.md
  unsafe {
    let mut low: u32; let mut high: u32;
    asm! ("rdtsc", lateout ("eax") low, lateout ("edx") high, options (nomem, nostack));
    ((high as u64) << 32) | (low as u64)}}

#[cfg(all(feature = "nightly", feature = "rdtsc"))]
#[test] fn test_rdtsc() {
  assert! (rdtsc() != rdtsc())}

/// Allows several threads or processes to compete for a shared resource by tracking resource ownership with a file.  
/// If the lock file is older than `ttl_sec` then it is removed, allowing us to recover from a thread or process dying while holding the lock.
pub struct FileLock<'a> {
  /// Filesystem path of the lock file.
  pub lock_path: &'a dyn AsRef<Path>,
  /// The time in seconds after which an outdated lock file can be removed.
  pub ttl_sec: f64,
  /// The owned lock file. Removed upon unlock.
  pub file: std::fs::File}
impl<'a> FileLock<'a> {
  /// Tries to obtain a file lock.
  /// 
  /// No blocking. Returns `None` if the file already exists and is recent enough (= locked).
  ///
  /// The returned structure will automatically remove the lock file when dropped.
  /// 
  ///     if let Some (lock) = try_s! (FileLock::lock (&"something.lock", 600.)) {
  ///       // ... Your code here ...
  ///       drop (lock)
  ///     }
  pub fn lock (lock_path: &'a dyn AsRef<Path>, ttl_sec: f64) -> Result<Option<FileLock<'a>>, String> {
    let mut cycle = 0u8;
    loop {
      if cycle > 1 {break Ok (None)}  // A second chance.
      cycle += 1;
      let mut fo = std::fs::OpenOptions::new();
      match fo.read (true) .write (true) .create_new (true) .open (lock_path.as_ref()) {
        Ok (file) => break Ok (Some (FileLock {lock_path, ttl_sec, file})),
        Err (ref ie) if ie.kind() == std::io::ErrorKind::AlreadyExists => {
          // See if the existing lock is old enough to be discarded.
          let lm = match last_modified_sec (lock_path) {
            Ok (lm) => lm,
            Err (ie) => break ERR! ("Error checking {:?}: {}", lock_path.as_ref(), ie)};
          if lm == 0. {continue}  // Unlocked already?
          if now_float() - lm > ttl_sec {
            if let Err (err) = std::fs::remove_file (lock_path.as_ref()) {break ERR! ("Error removing {:?}: {}", lock_path.as_ref(), err)}
            continue}
          break Ok (None)},
        Err (ie) => break ERR! ("Error creating {:?}: {}", lock_path.as_ref(), ie)}}}
  /// Updates the modification time on the lock file.
  /// Compile on Linux only as UTIME_NOW and futimens is absent on MacOS.
  #[cfg(target_os = "linux")]
  pub fn touch (&self) -> Result<(), String> {
    // TODO: Consider using https://crates.io/crates/filetime as an optional dependency
    let ts = libc::timespec {tv_sec: 0, tv_nsec: libc::UTIME_NOW};
    let times = [ts, ts];
    use std::os::unix::io::AsRawFd;
    let rc = unsafe {libc::futimens (self.file.as_raw_fd(), &times[0])};
    if rc != 0 {
      let err = std::io::Error::last_os_error();
      return ERR! ("Can't touch {:?}: {}", self.lock_path.as_ref(), err)}
    Ok(())}}
impl<'a> Drop for FileLock<'a> {
  fn drop (&mut self) {
    let _ = std::fs::remove_file (self.lock_path);}}
impl<'a> std::fmt::Debug for FileLock<'a> {
  fn fmt (&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    write! (f, "FileLock ({:?}, {})", self.lock_path.as_ref(), self.ttl_sec)}}

/// Process entry in /proc.
#[derive(Debug)]
pub struct ProcEn {
  pub name: String,
  pub path: std::path::PathBuf,
  /// NB: cmdline is NUL-separated (meaning there will be an empty string at the end)
  pub cmdline: Vec<String>}
impl ProcEn {
  pub fn pid (&self) -> Option<u32> {
    if let Some (file_name) = self.path.file_name() {
      if let Some (file_name) = file_name.to_str() {
        if let Ok (pid) = file_name.parse() {
          return Some (pid)}}}
    None}}
/// Iterate over processes in /proc.
///
///     if ProcIt::new().any (|proc_en| proc_en.cmdline.iter().any (|line_en| line_en.contains ("overfiend"))) {
///       println! ("Overfiend the daemon is live!");
///     }
///
///     let overfiends: Vec<ProcEn> = ProcIt::new().filter_map (|proc_en|
///       if proc_en.cmdline.iter().any (|line_en| line_en.contains ("overfiend")) {Some (proc_en)}
///       else {None}
///     ) .collect();
pub struct ProcIt {read_dir: std::fs::ReadDir}
impl ProcIt {
  pub fn new() -> ProcIt {
    ProcIt {
      read_dir: match Path::new ("/proc") .read_dir() {Ok (it) => it, Err (err) => panic! ("!proc: {}", err)}}}}
impl Iterator for ProcIt {
  type Item = ProcEn;
  fn next (&mut self) -> Option<ProcEn> {
    match self.read_dir.next() {
      None => return None,
      Some (Err (err)) => panic! ("ProcIt] !read_dir: {}", err),
      Some (Ok (proc_en)) => {
        let file_type = match proc_en.file_type() {
          Ok (ft) => ft,
          Err (err) => {
            if matches! (err.kind(), io::ErrorKind::NotFound) {
              return self.next()
            } else {
              panic! ("!file_type ({:?}): {}", proc_en.path(), err)}}};
        if !file_type.is_dir() {return self.next()}
        let name = proc_en.file_name();
        let name = match name.to_str() {Some (name) => name, None => panic! ("ProcIt] !to_str")};
        if !name.as_bytes().iter().all (|&b| b >= b'0' && b <= b'9') {  // Looks like PID?
          return self.next()}
        let path = proc_en.path();
        let cmdline = String::from_utf8 (slurp (&path.join ("cmdline"))) .expect ("!from_utf8");  // NB: cmdline is NUL-separated.
        if cmdline.is_empty() {return self.next()}
        Some (ProcEn {name: name.into(), path: path, cmdline: cmdline.split ('\0') .map (String::from) .collect()})}}}}

/// Reason for having this is that neither `multiqueue` nor `crossbeam_channel` implement UnwindSafe currently.
///
/// cf. https://github.com/crossbeam-rs/crossbeam-channel/issues/25.
///
/// Condvar is hopefully unwind-save since it's using a poisoning Mutex. Should unit-test it though.
pub mod oneshot {
  use std::panic::AssertUnwindSafe;
  use std::sync::{Arc, Condvar, Mutex};

  /// Accepts one value into the channel.
  pub struct Sender<T> (Arc<Mutex<Option<T>>>, Arc<AssertUnwindSafe<Condvar>>);
  impl<T> Sender<T> {
    pub fn send (self, v: T) {
      { let arc_mutex = self.0;  // Moving `self.0` in order to drop it first.
        { let lr = arc_mutex.lock();
          if let Ok (mut lock) = lr {*lock = Some (v)} } }
      self.1.notify_one()}}

  /// Returns the value from the channel.
  pub struct Receiver<T> (Arc<Mutex<Option<T>>>, Arc<AssertUnwindSafe<Condvar>>);
  impl<T> Receiver<T> {
    pub fn recv (self) -> Result<T, String> {
      let mut arc_mutex = self.0;
      let arc_condvar = self.1;
      loop {
        match Arc::try_unwrap (arc_mutex) {
          Ok (mutex) => {
            if let Some (value) = try_s! (mutex.into_inner()) {return Ok (value)}
            else {return ERR! ("recv] Sender gone without providing a value")}},
          Err (am) => {
            arc_mutex = am;
            let locked_value = try_s! (arc_mutex.lock());
            if locked_value.is_none() {let _locked_value = try_s! (arc_condvar.wait (locked_value));}}}}}}

  /// Create a new oneshot channel.
  pub fn oneshot<T>() -> (Sender<T>, Receiver<T>) {
    let arc_mutex = Arc::new (Mutex::new (None));
    let arc_condvar = Arc::new (AssertUnwindSafe (Condvar::new()));
    (Sender (arc_mutex.clone(), arc_condvar.clone()), Receiver (arc_mutex, arc_condvar))}}

#[test] fn test_oneshot() {
  let (tx, rx) = oneshot::oneshot();
  std::thread::spawn (|| tx.send (42));
  assert_eq! (42, rx.recv().expect("!recv"))}

/// Helps logging binary data (particularly with text-readable parts, such as bencode, netstring)
/// by replacing all the non-printable bytes with the `blank` character.
pub fn binprint (bin: &[u8], blank: u8) -> String {
  let mut bin: Vec<u8> = bin.into();
  for ch in bin.iter_mut() {if *ch < 0x20 || *ch >= 0x7F {*ch = blank}}
  unsafe {String::from_utf8_unchecked (bin)}}

/// Row-major bits, 2x3, to [Bedstead](https://i.imgur.com/f3myFgM.png)
/// 
/// cf. https://youtu.be/5yoWxctJsYo graphics with teletext; Windows font rendering glitch
pub fn bits2bedstead (ch: u32) -> char {
  let ch =
    if 0b111111 < ch {0xEE00}
    else if 32 <= ch {0xEE40 + ch - 32}
    else if 0 < ch {0xEE00 + ch}
    else {0xEE00 + ch};
  unsafe {char::from_u32_unchecked (ch)}}

/// [Bedstead](https://i.imgur.com/f3myFgM.png) to row-major bits, 2x3
pub fn bedstead2bits (ch: char) -> u32 {
  let ch = ch as u32;
  if 0xEE5F < ch {0}  // Past G1
  else if 0xEE40 <= ch {ch - 0xEE40 + 32}
  else if 0xEE00 <= ch {ch - 0xEE00}
  else {0}}  // Below G1

#[test]
fn test_bedstead() {
  for bits in 0 ..= 0b111111 {
    let ch = bits2bedstead (bits);
    assert_eq! (bits, bedstead2bits (ch))}}

pub fn round_to (decimals: u32, num: f32) -> f32 {
  let r = 10u32 .pow (decimals) as f32;
  (num * r) .round() / r}

/// Allows to sort by float, but panics if there's a NaN or infinity
#[derive(Clone, Copy, Debug, PartialOrd, PartialEq)]
pub struct OrdFloat (pub f64);
impl Eq for OrdFloat {}
impl Ord for OrdFloat {
  fn cmp (&self, other: &Self) -> std::cmp::Ordering {
    self.0.partial_cmp (&other.0) .expect ("!partial_cmp")}}
use std::hash::{Hash, Hasher};
impl Hash for OrdFloat {
  fn hash<H: Hasher> (&self, state: &mut H) {
    self.0.to_bits().hash (state)}}
impl std::fmt::Display for OrdFloat {
  fn fmt (&self, fm: &mut std::fmt::Formatter) -> std::fmt::Result {
    self.0.fmt (fm)}}
