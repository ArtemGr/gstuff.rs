#![feature(asm)]

#[macro_use] extern crate lazy_static;
extern crate libc;
extern crate term;
extern crate term_size;

use std::any::Any;
use std::fs;
use std::io;
use std::io::{Read, Write};
use std::path::Path;
use std::process::{Command, Stdio};
use std::str::from_utf8_unchecked;
use std::sync::Mutex;
use std::time::{Duration, SystemTime, UNIX_EPOCH};
#[cfg(test)] use std::thread::sleep;

/// Shortcut to path->filename conversion.
///
/// Returns the unchanged `path` if there is a character encoding error or something.
pub fn filename<'a> (path: &'a str) -> &'a str {
  match Path::new (path) .file_name() {
    Some (filename) => match filename.to_str() {
      Some (fstr) => if fstr.ends_with (".rs") {&fstr[0 .. fstr.len() - 3]} else {fstr},
      None => path},
    None => path}}

mod gstuff {pub fn filename<'a> (path: &'a str) -> &'a str {super::filename (path)}}

// A trick to use the `try_s` macro from both the outside and inside of the crate.
//mod gstuff {pub fn filename<'a> (path: &'a str) -> &'a str {::filename (path)}}

/// Returns on error, converting the `Err` value to `String` and prepending the current location.
///
/// cf. http://www.reddit.com/r/rust/comments/29wwzw/error_handling_and_result_types/cipcm9a
#[macro_export] macro_rules! try_s {
  ($e: expr) => {match $e {Ok (ok) => ok, Err (err) => {return Err (format! ("{}:{}] {}", ::gstuff::filename (file!()), line!(), err));}}}}

/// Returns on error, prepending the current location to a stringified error, then passing the string to `From::from`.
#[macro_export] macro_rules! try_f {
   ($e: expr) => {match $e {
     Ok (ok) => ok,
     Err (err) => {return Err (From::from (format! ("{}:{}] {}", ::gstuff::filename (file!()), line!(), err)));}}}}

/// Like `try_s`, but takes a reference.
#[macro_export] macro_rules! try_sp {
  ($e: expr) => {match $e {&Ok (ref ok) => ok,
    &Err (ref err) => {return Err (From::from (format! ("{}:{}] {:?}", ::gstuff::filename (file!()), line!(), err)));}}}}

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
    Err (err) => {return Box::new (futures::future::err (From::from (err)))}}}}

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
    Err (err) => {return Box::new (futures::future::err (ERRL! ("{}", err)))}}}}

/// Prepends file name and line number to the given message.
#[macro_export] macro_rules! ERRL {
  ($format: expr, $($args: tt)+) => {format! (concat! ("{}:{}] ", $format), ::gstuff::filename (file!()), line!(), $($args)+)};
  ($format: expr) => {format! (concat! ("{}:{}] ", $format), ::gstuff::filename (file!()), line!())}}

/// Returns a `Err(String)`, prepending the current location (file name and line number) to the string.
///
/// Examples: `ERR! ("too bad")`; `ERR! ("{}", foo)`;
#[macro_export] macro_rules! ERR {
  ($format: expr, $($args: tt)+) => {Err (ERRL! ($format, $($args)+))};
  ($format: expr) => {Err (ERRL! ($format))}}

/// --- status line -------

lazy_static! {
  static ref STATUS_LINE: Mutex<String> = Mutex::new (String::new());
  /// True if the standard output is a terminal.
  pub static ref ISATTY: bool = unsafe {libc::isatty (1)} != 0;}

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
pub fn status_line (file: &str, line: u32, status: String) {
  use std::collections::hash_map::DefaultHasher;
  use std::hash::Hasher;

  if let Some (mut stdout) = term::stdout() {
    if let Ok (mut status_line) = STATUS_LINE.lock() {
      let old_hash = {let mut hasher = DefaultHasher::new(); hasher.write (status_line.as_bytes()); hasher.finish()};
      status_line.clear();
      use std::fmt::Write;
      let _ = write! (&mut *status_line, "{}:{}] {}", filename (file), line, status);
      let new_hash = {let mut hasher = DefaultHasher::new(); hasher.write (status_line.as_bytes()); hasher.finish()};
      if old_hash != new_hash {
        // Try to keep the status line withing the terminal bounds.
        match term_size::dimensions() {
          Some ((w, _)) if status_line.chars().count() >= w => {
            let mut tmp = String::with_capacity (w - 1);
            for ch in status_line.chars().take (w - 1) {tmp.push (ch)}
            let _ = stdout.get_mut().write (tmp.as_bytes());},
          _ => {let _ = stdout.get_mut().write (status_line.as_bytes());}};

        // Clear the rest of the line.

        // NB: term's `delete_line` is really screwed.
        // Sometimes it doesn't work. And when it does, it does it wrong.
        // Documentation says it "Deletes the text from the cursor location to the end of the line"
        // but when it works it clears the *entire* line instead.
        // I should probably find something better than term, unless it's `delete_line` is fixed first.

        //let _ = stdout.delete_line();
        let _ = stdout.get_mut().write (b"\x1B[K");  // EL0. Clear right.

        let _ = stdout.carriage_return();
        let _ = stdout.get_mut().flush();}}}}

/// Clears the status line ff stdout `isatty` and `status_line` isn't empty.
pub fn status_line_clear() {
  if let Ok (mut status_line) = STATUS_LINE.lock() {
    if *ISATTY && !status_line.is_empty() {
      if let Some (mut stdout) = term::stdout() {
        status_line.clear();
        //let _ = stdout.delete_line();
        let _ = stdout.get_mut().write (b"\x1B[K");  // EL0. Clear right.
        let _ = stdout.get_mut().flush();}}}}

/// Clear the status line, run the code, then restore the status line.
///
/// Simply runs the `code` if the stdout is not `isatty` or if the status line is empty.
pub fn with_status_line (code: &Fn()) {
  if let Ok (status_line) = STATUS_LINE.lock() {
    if !*ISATTY || status_line.is_empty() {
      code()
    } else if let Some (mut stdout) = term::stdout() {
      //let _ = stdout.delete_line();
      let _ = stdout.get_mut().write (b"\x1B[K");  // EL0. Clear right.
      let _ = stdout.get_mut().flush();  // We need to send this EL0 out because the $code might be writing to stderr and thus miss it.
      code();
      // TODO: Should probably use `term_size::dimensions` to limit the status line size, just like in `fn status_line`.
      let _ = stdout.get_mut().write (status_line.as_bytes());
      let _ = stdout.carriage_return();
      let _ = stdout.get_mut().flush();}}}

#[test] fn test_status_line() {
  with_status_line (&|| println! ("hello world"));}

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
pub fn with_hostname (visitor: &mut FnMut (&[u8])) -> Result<(), std::io::Error> {
  use libc::{size_t, gethostname};  // http://man7.org/linux/man-pages/man2/gethostname.2.html
  use std::ffi::CStr;
  use std::io;

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
pub fn slurp (path: &AsRef<Path>) -> Vec<u8> {
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
    Err (ref err) if err.kind() == io::ErrorKind::NotFound => {  // "sh" was not found, try a different name.
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
///    if let Err (err) = catch_unwind (AssertUnwindSafe (move || {
///      let mut core = tokio_core::reactor::Core::new().expect ("!core");
///      loop {core.turn (None)}
///    })) {println! ("CORE panic! {:?}", any_to_str (&*err)); std::process::abort()}
pub fn any_to_str<'a> (message: &'a Any) -> Option<&'a str> {
  if let Some (message) = message.downcast_ref::<&str>() {return Some (message)}
  if let Some (message) = message.downcast_ref::<String>() {return Some (&message[..])}
  return None}

/// Converts the duration into a number of seconds with fractions.
pub fn duration_to_float (duration: Duration) -> f64 {
  duration.as_secs() as f64 + ((duration.subsec_nanos() as f64) / 1000000000.0)}

/// The current number of seconds since the UNIX epoch, with fractions.
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
  assert! (delta > 0.098 && delta < 0.102, "delta: {}", delta);}

/// Last-modified of the file in seconds since the UNIX epoch, with fractions.  
/// Returns 0 if the file does not exists.
///
/// A typical use case:
///
///     if (now_float() - try_s! (last_modified_sec (&path)) > 600.) {update (&path)}
pub fn last_modified_sec (path: &AsRef<Path>) -> Result<f64, String> {
  let meta = match path.as_ref().metadata() {
    Ok (m) => m,
    Err (ref err) if err.kind() == std::io::ErrorKind::NotFound => return Ok (0.),
    Err (err) => return ERR! ("{}", err)};
  let lm = try_s! (meta.modified());
  let lm = duration_to_float (try_s! (lm.duration_since (UNIX_EPOCH)));
  Ok (lm)}

// --- nom extensions ---

/// Implements the `/(?x) (.*?) (remainder)/` pattern:
/// looks for remainder first, then returns a tuple with the prefix and the remainder.
///
/// Discussion: https://www.reddit.com/r/rust/comments/4yokxd/crash_course_into_nom_kind_of_question/
///
/// Example iterating over an `input`:
///
///         let mut pos = input;
///         while let IResult::Done (tail, (_head, _parsed_remainder)) = take_until_parse_s! (pos, tag! ("remainder")) {
///             pos = tail
///         }
#[macro_export]
macro_rules! take_until_parse_s (
  ($i: expr, $remainder: ident! ($($args:tt)*)) => ({
    let input: &str = $i;
    let mut ret = IResult::Error (error_position! (nom::ErrorKind::Custom (0), input));
    for (pos, _) in $i.char_indices() {
      match $remainder! (&input[pos..], $($args)*) {
        IResult::Done (i,o)    => {ret = IResult::Done (i, (&input[0..pos], o)); break},  // Found the remainder!
        IResult::Error(_)      => continue,  // Keep looking.
        IResult::Incomplete(_) => continue}}  // Keep looking.

    if !ret.is_done() {
      // Last chance. See if subparser accepts an empty string.
      if let IResult::Done (i,o) = $remainder! ("", $($args)*) {
        ret = IResult::Done (i, (input, o))}}  // Empty remainder was accepted.

    ret});

  ($i: expr, $f: expr) => (take_until_parse_s! ($i, call! ($f));););

// TODO: Should also implement the pattern interfaces at https://doc.rust-lang.org/nightly/std/str/pattern/index.html
//       in order to search and replace with nom.

/// Uses nom to find all matches of the given `$submac` parser and replace them with the `$submac` results.
///
/// For exaple, replacing "foo" with "bar" might look like this:
///
///     use nom::{self, IResult};
///     let bar_bar = parse_replace_s! ("foo bar", map! (tag_s! ("foo"), |_| "bar"));
#[macro_export]
macro_rules! parse_replace_s {
  ($i: expr, $submac: ident! ($($args:tt)*)) => ({
    let input: &str = $i;
    let mut output = String::with_capacity (input.len() * 2 + 32);
    let mut pos = input;
    while let IResult::Done (tail, (head, evaluation)) = take_until_parse_s! (pos, $submac! ($($args)*)) {
      output.push_str (head);
      output.push_str (&evaluation);
      pos = tail;}
    output.push_str (pos);
    output});

  ($i: expr, $f: expr) => (parse_replace_s! ($i, call! ($f)););}

/// `$starts` is an optional `Pattern` used to optimize the `$remainder` search.
///
/// For example, with jetscii: `take_until_find_parse_s! ("foo bar", ascii_chars! ('b'), tag_s! ("bar"))`.
#[macro_export]
macro_rules! take_until_find_parse_s (
  ($i: expr, $starts: expr, $remainder: ident! ($($args:tt)*)) => ({
    let input: &str = $i;
    let mut ret = IResult::Error (error_position! (nom::ErrorKind::Custom (0), input));
    for (pos, _) in $i.match_indices ($starts) {
      match $remainder! (&input[pos..], $($args)*) {
        IResult::Done (i,o)    => {ret = IResult::Done (i, (&input[0..pos], o)); break},  // Found the remainder!
        IResult::Error(_)      => continue,  // Keep looking.
        IResult::Incomplete(_) => continue}}  // Keep looking.
    ret});

  ($i: expr, $starts: expr, $f: expr) => (take_until_find_parse_s! ($i, $starts, call! ($f));););

/// Uses nom to find all matches of the given `$submac` parser and replace them with the parser's evaluations.
///
/// `$starts` is a `Pattern` that is used to speed up the search. It must match the beginning of any `$submac`-compatible substrings.
///
/// For exaple, replacing "foo" with "bar" might look like this:
///
///     use nom::{self, IResult};
///     let bar_bar = find_parse_replace_s! ("foo bar", ascii_chars! ('f'), map! (tag_s! ("foo"), |_| "bar"));
#[macro_export]
macro_rules! find_parse_replace_s {
  ($i: expr, $starts: expr, $submac: ident! ($($args:tt)*)) => ({
    let input: &str = $i;
    let mut output = String::with_capacity (input.len() * 2 + 32);
    let mut pos = input;
    while let IResult::Done (tail, (head, evaluation)) =
      take_until_find_parse_s! (pos, $starts, $submac! ($($args)*)) {
        output.push_str (head);
        output.push_str (&evaluation);
        pos = tail;}
    output.push_str (pos);
    output});

  ($i: expr, $starts: expr, $f: expr) => (find_parse_replace_s! ($i, $starts, call! ($f)););}

/// Time Stamp Counter (number of cycles).
pub fn rdtsc() -> u64 {  // http://stackoverflow.com/a/7617612/257568; https://github.com/gz/rust-x86/blob/master/src/bits64/time.rs
  #[allow(unused_mut)] unsafe {
    let mut low: u32; let mut high: u32;
    asm!("rdtsc" : "={eax}" (low), "={edx}" (high));
    ((high as u64) << 32) | (low as u64)}}

/// Allows several threads or processes to compete for a shared resource by tracking resource ownership with a file.  
/// If the lock file is older than `ttl_sec` then it is removed, allowing us to recover from a thread or process dying while holding the lock.
pub struct FileLock<'a> {
  /// Filesystem path of the lock file.
  pub lock_path: &'a AsRef<Path>,
  /// The time in seconds after which an outdated lock file can be removed.
  pub ttl_sec: f64,
  /// The owned lock file. Removed upon unlock.
  pub file: std::fs::File}
impl<'a> FileLock<'a> {
  /// Tries to obtain a file lock.
  /// 
  /// Returns `None` if the file already exists and is recent enough.
  ///
  /// The returned structure will automatically remove the lock file when dropped.
  /// 
  ///     if let Some (lock) = try_s! (FileLock::lock (&"something.lock", 600.)) {
  ///       // ... Your code here ...
  ///       drop (lock)
  ///     }
  pub fn lock (lock_path: &'a AsRef<Path>, ttl_sec: f64) -> Result<Option<FileLock<'a>>, String> {
    let mut cycle = 0u8;
    loop {
      if cycle > 1 {break Ok (None)}  // A second chance.
      cycle += 1;
      match std::fs::OpenOptions::new().write (true) .create_new (true) .open (lock_path.as_ref()) {
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
  #[cfg(unix)]
  fn touch (&self) -> Result<(), String> {
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
  /// NB: cmdline is NUL-separated.
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
        let file_type = match proc_en.file_type() {Ok (ft) => ft, Err (err) => panic! ("!file_type: {}", err)};
        if !file_type.is_dir() {return self.next()}
        let name = proc_en.file_name();
        let name = match name.to_str() {Some (name) => name, None => panic! ("ProcIt] !to_str")};
        if !name.as_bytes().iter().all (|&b| b >= b'0' && b <= b'9') {  // Looks like PID?
          return self.next()}
        let path = proc_en.path();
        let cmdline = String::from_utf8 (slurp (&path.join ("cmdline"))) .expect ("!from_utf8");  // NB: cmdline is NUL-separated.
        if cmdline.is_empty() {return self.next()}
        Some (ProcEn {name: name.into(), path: path, cmdline: cmdline.split ('\0') .map (String::from) .collect()})}}}}
