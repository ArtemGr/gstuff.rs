#![allow(unknown_lints, uncommon_codepoints)]
#![allow(unused_imports)]

#![cfg_attr(feature = "nightly", feature(test))]

#![cfg_attr(feature = "re", feature(try_trait_v2))]
#![cfg_attr(feature = "re", feature(never_type))]

extern crate libc;
#[cfg(feature = "crossterm")] extern crate crossterm;

//use std::fmt;
//use std::marker::PhantomData;
use core::any::Any;
use core::arch::asm;
use core::str::from_utf8_unchecked;
use core::sync::atomic::{AtomicI8, AtomicUsize, Ordering};
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
static mut STATUS_LINE: Mutex<String> = Mutex::new (String::new());

#[cfg(feature = "crossterm")]
pub struct IsTty {pub is_tty: AtomicI8}
#[cfg(feature = "crossterm")]
impl core::ops::Deref for IsTty {
  type Target = bool;
  fn deref (&self) -> &Self::Target {
    let mut is_tty = self.is_tty.load (Ordering::Relaxed);
    if is_tty == 0 {
      // https://man7.org/linux/man-pages/man3/isatty.3.html
      is_tty = if isatty (1) != 0 {1} else {-1};
      self.is_tty.store (is_tty, Ordering::Relaxed)}
    if is_tty == 1 {&true} else {&false}}}

/// `1` if standard output is a terminal, `0` if unknown
#[cfg(feature = "crossterm")]
pub static ISATTY: IsTty = IsTty {is_tty: AtomicI8::new (0)};

#[cfg(feature = "crossterm")]
pub static STATUS_LINE_LM: AtomicUsize = AtomicUsize::new (0);

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

  // NB: term's `delete_line` is really screwed.
  // Sometimes it doesn't work. And when it does, it does it wrong.
  // Documentation says it "Deletes the text from the cursor location to the end of the line"
  // but when it works it clears the *entire* line instead.
  // let _ = stdout.write (b"\x1B[K");}}  // EL0. Clear right.

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
///       status_line (file!(), line!(), &fomat! ($($args)+))}}}
#[cfg(all(feature = "crossterm"))]
pub fn status_line (file: &str, line: u32, status: &str) {
  use crossterm::{QueueableCommand, cursor};
  use io::{stdout, Write};
  use std::collections::hash_map::DefaultHasher;
  use std::hash::Hasher;

    if let Ok (mut status_line) = unsafe {STATUS_LINE.lock()} {
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
pub fn status_line_clear() -> String {
  use io::{stdout, Write};
  let mut ret = String::new();
  if let Ok (mut status_line) = unsafe {STATUS_LINE.lock()} {
    if *ISATTY && !status_line.is_empty() {
      let mut stdout = stdout();
        STATUS_LINE_LM.store (now_ms() as usize, Ordering::Relaxed);
        core::mem::swap (&mut ret, &mut status_line);
        delete_line (&mut stdout);
        let _ = stdout.flush();}}
  ret}

/// Clear the status line, run the code, then restore the status line.
///
/// Simply runs the `code` if the stdout is not `isatty` or if the status line is empty.
#[cfg(feature = "crossterm")]
pub fn with_status_line (code: &dyn Fn()) {
  use crossterm::{QueueableCommand, cursor};
  use io::{stdout, Write};

  if let Ok (status_line) = unsafe {STATUS_LINE.lock()} {
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

#[cfg(all(feature = "crossterm", feature = "chrono"))]
pub fn short_log_time (ms: u64)
-> chrono::format::DelayedFormat<chrono::format::strftime::StrftimeItems<'static>> {
  use chrono::{Local, LocalResult, TimeZone};
  if let Some (time) = Local.timestamp_millis_opt (ms as i64) .earliest() {
    time.format ("%d %H:%M:%S")
  } else {
    Local::now().format ("00 00:00:00")}}

#[cfg(all(feature = "crossterm", feature = "chrono", feature = "fomat-macros"))]
#[macro_export] macro_rules! log {

  (0, $($args: tt)+) => {  // (temporarily) disable
    if 1 == 0 {log! ($($args)+)}};
  (1, $($args: tt)+) => {  // proceed as usual
    {log! ($($args)+)}};

  (t $time: expr => $delay: expr, $($args: tt)+) => {{  // $delay repeat by $time
    static LL: core::sync::atomic::AtomicI64 = core::sync::atomic::AtomicI64::new (0);
    let now = $time as i64;
    let Δ = now - LL.load (core::sync::atomic::Ordering::Relaxed);
    if $delay <= Δ {
      LL.store (now, core::sync::atomic::Ordering::Relaxed);
      log! ($($args)+)}}};

  (q $command: expr, $($args: tt)+) => {{
    $crate::with_status_line (&|| {
      use crossterm::QueueableCommand;
      use fomat_macros::{wite, fomat};
      use std::io::Write;
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
///     use core::mem::MaybeUninit;
///     use std::io::Write;
///     #[allow(invalid_value)] let mut foobar: [u8; 128] = unsafe {MaybeUninit::uninit().assume_init()};
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
  let s = unsafe {::core::str::from_utf8_unchecked (&$array[0..end])};
  s}}}

/// Fomat into a small string.
/// 
/// Typical imports:
/// 
///     use inlinable_string::{InlinableString, StringExt};
///     use std::fmt::{Write as FmtWrite};
#[cfg(feature = "fomat-macros")]
#[macro_export] macro_rules! ifomat {
  ($($args: tt)+) => ({
    use inlinable_string::{InlinableString, StringExt};
    use std::fmt::Write as FmtWrite;
    let mut is = InlinableString::new();
    wite! (&mut is, $($args)+) .expect ("!wite");
    is})}

/// now_ms / 1000 / 86400 ↦ year, month, day UTC
/// 
/// https://stackoverflow.com/a/32158604/257568
pub fn civil_from_days (mut z: i32) -> (i32, u32, u32) {
  z += 719468;
  let era = if 0 <= z {z} else {z - 146096} / 146097;
  let doe = (z - era * 146097) as u32;  // 0..=146096
  let yoe = (doe - doe/1460 + doe/36524 - doe/146096) / 365;  // 0..=399
  let y = yoe as i32 + era * 400;
  let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);  // 0..=365
  let mp = (5 * doy + 2) / 153;  // 0..=11
  let d = doy - (153 * mp + 2) / 5 + 1;  // 1..=31
  let m = (mp as i32 + if (mp as i32) < 10 {3} else {-9}) as u32;  // 1..=12
  (y + if m <= 2 {1} else {0}, m, d)}

/// year, month 1..=12, day 1..=31 UTC ↦ UNIX milliseconds (aka now_ms) / 1000 / 86400
pub fn days_from_civil (mut y: i32, m: u32, d: u32) -> i32 {
  y -= if m <= 2 {1} else {0};
  let era = if 0 <= y {y} else {y - 399} / 400;
  let yoe = (y - era * 400) as u32;      // 0..=399
  let doy = (153 * (m as i32 + (if 2 < m {-3} else {9})) + 2) as u32 / 5 + d - 1;  // 0..=365
  let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;  // 0..=146096
  era * 146097 + doe as i32 - 719468}

/// into integer with centiseconds "%y%m%d%H%M%S%.2f"
#[cfg(feature = "chrono")]
pub fn ldt2ics (dt: &chrono::DateTime<chrono::Local>) -> i64 {
  use chrono::{Datelike, Timelike};
  let y = dt.year() as i64;
  let m = dt.month() as i64;
  let d = dt.day() as i64;
  let ti = dt.time();
  let h = ti.hour() as i64;
  let min = ti.minute() as i64;
  let s = ti.second() as i64;
  let cs = ti.nanosecond() as i64 / 10000000;
  y%1000 * 1e12 as i64 + m * 10000000000 + d * 100000000 + h * 1000000 + min * 10000 + s * 100 + cs}

/// UNIX time into ISO 8601 "%Y-%m-%dT%H:%M:%S%.3fZ", UTC
#[cfg(all(feature = "inlinable_string"))]
pub fn ms2iso8601 (ms: i64) -> inlinable_string::InlinableString {
  use inlinable_string::{InlinableString, StringExt};
  use std::fmt::Write as FmtWrite;
  let day = (ms / 1000 / 86400) as i32;
  let h = ((ms / 1000) % 86400) / 3600;
  let min = ((ms / 1000) % 3600) / 60;
  let s = (ms / 1000) % 60;
  let ms = ms % 1000;
  let (y, m, d) = civil_from_days (day);
  let mut is = inlinable_string::InlinableString::new();
  // NB: Here `write!` is faster than `wite!`
  write! (&mut is, "{:04}-{:02}-{:02}T{:02}:{:02}:{:02}.{:03}Z", y, m, d, h, min, s, ms) .expect ("!write!");
  is}

/// UNIX time into integer with centiseconds "%y%m%d%H%M%S%.2f", UTC
pub fn ms2ics (ms: i64) -> i64 {
  let day = (ms / 1000 / 86400) as i32;
  let h = ((ms / 1000) % 86400) / 3600;
  let min = ((ms / 1000) % 3600) / 60;
  let s = (ms / 1000) % 60;
  let cs = ms % 1000 / 10;
  let (y, m, d) = civil_from_days (day);
  let y = y as i64; let m = m as i64; let d = d as i64;
  y%1000 * 1e12 as i64 + m * 10000000000 + d * 100000000 + h * 1000000 + min * 10000 + s * 100 + cs}

/// integer with centiseconds "%y%m%d%H%M%S%.2f" into UNIX time in milliseconds
pub fn ics2ms (ics: i64) -> i64 {
  let day = days_from_civil (
    (ics / 1000000000000 + 2000) as i32,
    (ics / 10000000000 % 100) as u32,
    (ics / 100000000 % 100) as u32) as i64;
  let tm_hour = (ics / 1000000 % 100) as i64;
  let tm_min = (ics / 10000 % 100) as i64;
  let tm_sec = (ics / 100 % 100) as i64;
  let ms = (ics % 100 * 10) as i64;
  ms + tm_sec * 1000 + tm_min * 60000 + tm_hour * 3600000 + day * 86400000}

/// from integer with centiseconds "%y%m%d%H%M%S%.2f"
#[cfg(all(feature = "chrono", feature = "re"))]
pub fn ics2ldt (ims: i64) -> re::Re<chrono::DateTime<chrono::Local>> {
  use chrono::{TimeZone, Timelike};
  let dt = chrono::Local.with_ymd_and_hms (
    (ims / 1000000000000 + 2000) as i32,
    (ims / 10000000000 % 100) as u32,
    (ims / 100000000 % 100) as u32,
    (ims / 1000000 % 100) as u32,
    (ims / 10000 % 100) as u32,
    (ims / 100 % 100) as u32) .earliest()?;
  let dt = dt.with_nanosecond ((ims % 100) as u32 * 10000000)?;
  re::Re::Ok (dt)}

/// from integer with centiseconds "%y%m%d%H%M%S%.2f"
#[cfg(all(feature = "chrono", feature = "re"))]
pub fn ics2ndt (ims: i64) -> re::Re<chrono::NaiveDateTime> {
  use chrono::{TimeZone, Timelike};
  let dt = chrono::NaiveDateTime::new (
    chrono::NaiveDate::from_ymd_opt (
      (ims / 1000000000000 + 2000) as i32,
      (ims / 10000000000 % 100) as u32,
      (ims / 100000000 % 100) as u32)?,
    chrono::NaiveTime::from_hms_nano_opt (
      (ims / 1000000 % 100) as u32,
      (ims / 10000 % 100) as u32,
      (ims / 100 % 100) as u32,
      (ims % 100) as u32 * 10000000)?);
  re::Re::Ok (dt)}

/// Extend ISO 8601 shorthand into full RFC 3339 timestamp.  
/// “2022-12-12T12” → “2022-12-12T12:00:00Z”
#[cfg(feature = "fomat-macros")]
#[macro_export] macro_rules! iso8601z {
  ($date_or_time: expr) => {{
    let sufff = ($date_or_time.len() as i32 - 10) .max (0) as usize;
    ifomat! (($date_or_time) if sufff < 10 {(&"T00:00:00Z"[sufff..])})}}}

/// ISO 8601 shorthand “2022-12-12T12” parsed as a Local
#[cfg(feature = "fomat-macros")]
#[macro_export] macro_rules! iso8601toL {($short: expr) => {
  Local.from_local_datetime (&(DateTime::parse_from_rfc3339 (&iso8601z! ($short))?) .naive_utc()) .earliest()?}}

/// ISO 8601 shorthand “2022-12-12T12” converted into integer with centiseconds "%y%m%d%H%M%S%.2f"
pub fn iso8601ics (iso: &[u8]) -> i64 {
  let mut ics: [u8; 14] = *b"00000000000000";
  if 4 <= iso.len() {
    ics[0] = iso[2]; ics[1] = iso[3];
    if 7 <= iso.len() && iso[4] == b'-' {
      ics[2] = iso[5]; ics[3] = iso[6];
      if 10 <= iso.len() && iso[7] == b'-' {
        ics[4] = iso[8]; ics[5] = iso[9];
        if 13 <= iso.len() && (iso[10] == b'T' || iso[10] == b' ') {
          ics[6] = iso[11]; ics[7] = iso[12];
          if 16 <= iso.len() && iso[13] == b':' {
            ics[8] = iso[14]; ics[9] = iso[15];
            if 19 <= iso.len() && iso[16] == b':' {
              ics[10] = iso[17]; ics[11] = iso[18];
              if 22 <= iso.len() && iso[19] == b'.' {
                ics[12] = iso[20]; ics[13] = iso[21]}}}}}}}
  match unsafe {std::str::from_utf8_unchecked (&ics)} .parse() {Ok (k) => k, Err (_err) => 0}}

#[cfg(all(test, feature = "nightly", feature = "chrono", feature = "inlinable_string", feature = "re"))] mod time_bench {
  extern crate test;
  use chrono::{DateTime, Datelike, Local, NaiveDateTime, TimeZone, Timelike, Utc};
  use crate::{civil_from_days, days_from_civil, ics2ldt, ics2ms, ics2ndt, iso8601ics, ldt2ics, ms2ics, ms2iso8601, now_ms, re::Re};
  use fomat_macros::wite;
  use inlinable_string::InlinableString;
  use rand::{rngs::SmallRng, seq::index::sample, Rng, SeedableRng};
  use test::black_box;

  #[bench] fn duration (bm: &mut test::Bencher) {
    assert! (946684800000 == days_from_civil (2000, 1, 1) as i64 * 86400 * 1000);
    let duration = 118050;
    assert! ("00:01:58.050" == &ms2iso8601 (946684800000 + duration) [11..23]);
    assert! (      15805 == ms2ics (946684800000 + duration) - 10100000000);
    let mut ms = 0;
    bm.iter (|| {  // verify that `ms2ics` can be reused to examine a time delta
      let ics = ms2ics (946684800000 + ms as i64) - 10100000000;
      let tm_min = (ics / 10000 % 100) as i64;
      let tm_sec = (ics / 100 % 100) as i64;
      let ims = (ics % 100 * 10) as i64;
      let msʹ = ims + tm_sec * 1000 + tm_min * 60000;
      assert! (ms == msʹ);
      ms += 10;
      if 3600 * 1000 <= ms {ms = 0}})}

  #[bench] fn iso8601icsᵇ (bm: &mut test::Bencher) {
    assert! (00000000000000 == iso8601ics (b""));
    assert! (24000000000000 == iso8601ics (b"2024"));
    assert! (24120000000000 == iso8601ics (b"2024-12"));
    assert! (24121300000000 == iso8601ics (b"2024-12-13"));
    assert! (24121321000000 == iso8601ics (b"2024-12-13T21"));
    assert! (24121321000000 == iso8601ics (b"2024-12-13T21+03"));
    assert! (24121314150000 == iso8601ics (b"2024-12-13T14:15"));
    assert! (24121314150000 == iso8601ics (b"2024-12-13 14:15"));
    assert! (24121314151600 == iso8601ics (b"2024-12-13T14:15:16"));
    assert! (24121314151600 == iso8601ics (b"2024-12-13 14:15:16"));
    assert! (24121314151698 == iso8601ics (b"2024-12-13T14:15:16.98"));
    assert! (24121314151698 == iso8601ics (b"2024-12-13T14:15:16.980"));
    assert! (24121314151698 == iso8601ics (b"3024-12-13T14:15:16.980Z"));
    assert! (24121314151698 == iso8601ics (b"2024-12-13T14:15:16.980-03"));
    bm.iter (|| {
      let ics = iso8601ics (b"4321-12-23T13:14:15.987");
      assert! (black_box (ics) == 21122313141598, "{}", ics)})}

  #[bench] fn ms2iso8601ᵇ (bm: &mut test::Bencher) {
    let mut rng = SmallRng::seed_from_u64 (now_ms());
    bm.iter (|| {
      let it = ms2iso8601 (rng.gen::<i64>().abs());
      assert! (black_box (it) .ends_with ('Z'))})}

  #[bench] fn chrono_iso8601 (bm: &mut test::Bencher) {
    let dt = Utc::now();
    bm.iter (|| {
      let it = ifomat! ((dt.format ("%Y-%m-%dT%H:%M:%S%.3fZ")));
      assert! (it.ends_with ('Z'))})}

  fn make_samples() -> Vec<(DateTime<Local>, InlinableString)> {
    let mut rng = SmallRng::seed_from_u64 (now_ms());
    let mut samples = Vec::with_capacity (65536);
    while samples.len() < samples.capacity() {
      let ms = rng.gen::<i64>().abs() / 10 * 10;
      if let Some (udt) = Utc.timestamp_millis_opt (ms) .earliest() {
        let day = (ms / 1000 / 86400) as i32;
        let (y, m, d) = civil_from_days (day);
        assert! (udt.year() == y && udt.month() == m && udt.day() == d, "{:?}, y{}, m{}, d{}", udt, y, m, d);
        assert! (days_from_civil (y, m, d) == day);
        let cit = ifomat! ((udt.format ("%Y-%m-%dT%H:%M:%S%.3fZ")));
        let cit = if cit.starts_with ('+') {&cit[1..]} else {&cit};
        let dit = ms2iso8601 (ms);
        assert! (cit == dit, "{} <> {}", cit, dit);
        if let Some (udt) = udt.with_year (2000 + udt.year() % 100) {
          let ms = udt.timestamp_millis();
          let ics = ms2ics (ms);
          let udtʹ = Utc.from_utc_datetime (&ics2ndt (ics) .unwrap());
          assert! (udt == udtʹ, "{:?} <> {:?}", udt, udtʹ);
          let msʹ = ics2ms (ics);
          assert! (ms == msʹ, "{} <> {}", ms, msʹ)}}
      if let Some (ldt) = Local.timestamp_millis_opt (ms) .earliest() {
        if let Some (ldt) = ldt.with_year (2000 + ldt.year() % 100) {
          let sdt = ifomat! ((ldt.format ("%Y-%m-%dT%H:%M:%S%.3f")));
          samples.push ((ldt, sdt))}}}
    samples}

  #[bench] fn iso8601tol (bm: &mut test::Bencher) {
    let (samples, mut sx) = (make_samples(), 0);
    bm.iter (|| {
      let ics = iso8601ics (samples[sx].1.as_bytes());
      let dt = ics2ldt (ics) .unwrap();
      let odt = &samples[sx].0;
      assert! (
        dt.year() == odt.year() && dt.month() == odt.month() && dt.day() == odt.day()
         && dt.hour() == odt.hour() && dt.minute() == odt.minute() && dt.second() == odt.second()
         && dt.nanosecond() == odt.nanosecond(),
        "{} {} <> {} {}", ics, dt, samples[sx].1, odt);
      sx += 1; if samples.len() <= sx {sx = 0}})}

  #[bench] fn iso8601ton (bm: &mut test::Bencher) {
    let (samples, mut sx) = (make_samples(), 0);
    bm.iter (|| {
      let ics = iso8601ics (samples[sx].1.as_bytes());
      let dt = ics2ndt (ics) .unwrap();
      let odt = &samples[sx].0;
      assert! (
        dt.year() == odt.year() && dt.month() == odt.month() && dt.day() == odt.day()
         && dt.hour() == odt.hour() && dt.minute() == odt.minute() && dt.second() == odt.second()
         && dt.nanosecond() == odt.nanosecond(),
        "{} {} <> {} {}", ics, dt, samples[sx].1, odt);
      sx += 1; if samples.len() <= sx {sx = 0}})}

  #[bench] fn chrono_from_str (bm: &mut test::Bencher) {bm.iter (|| {
    let dt = NaiveDateTime::parse_from_str ("4321-12-23T13:14:15", "%Y-%m-%dT%H:%M:%S") .unwrap();
    assert! (dt.year() == 4321 && dt.month() == 12 && dt.day() == 23 
      && dt.hour() == 13 && dt.minute() == 14 && dt.second() == 15)})}

  #[bench] fn chrono_from_rfc3339 (bm: &mut test::Bencher) {bm.iter (|| {
    let dt = DateTime::parse_from_rfc3339 ("4321-12-23T13:14:15Z") .unwrap();
    assert! (dt.year() == 4321 && dt.month() == 12 && dt.day() == 23
      && dt.hour() == 13 && dt.minute() == 14 && dt.second() == 15)})}

  #[bench] fn iso8601tol_macro (bm: &mut test::Bencher) {bm.iter (|| {
    fn f() -> Re<DateTime<Local>> {Re::Ok (iso8601toL! ("4321-12-23T13:14:15"))}
    let dt = f().unwrap();
    assert! (dt.year() == 4321 && dt.month() == 12 && dt.day() == 23
      && dt.hour() == 13 && dt.minute() == 14 && dt.second() == 15)})}

  #[bench] fn iso8601_ics_ms (bm: &mut test::Bencher) {bm.iter (|| {
    let ics = iso8601ics (black_box (b"4321-12-23T13:14:15"));
    assert! (ics == 21122313141500);
    assert! (ics2ms (black_box (ics)) == 1640265255000)})}}

/// Takes a netstring from the front of the slice.
///
/// Returns the unpacked netstring and the remainder of the slice.
///
/// NB: Netstring encoding is not included as a separate function
/// because it is as simple as `wite! (&mut buf, (payload.len()) ':' (payload) ',')?;`.
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
/// 
/// (There's now a native `Duration::as_secs_f64`.)
pub fn duration_to_float (duration: Duration) -> f64 {
  duration.as_secs() as f64 + ((duration.subsec_nanos() as f64) / 1000000000.0)}

/// Converts the time into a number of seconds with fractions.
#[cfg(feature = "chrono")]
pub fn dtl2float (dt: chrono::DateTime<chrono::Local>) -> f64 {
  dt.timestamp() as f64 + ((dt.timestamp_subsec_nanos() as f64) / 1000000000.0)}

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
  ///     let Some (lock) = FileLock::lock (&lockᵖ, 123.)? else {log! ("Locked."); return Re::Ok(())};
  ///     // ... Your code here ...
  ///     drop (lock)
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
    //⌥ switch to https://doc.rust-lang.org/nightly/std/fs/struct.File.html#method.set_times
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

pub fn round8 (decimals: u32, num: f64) -> f64 {
  let r = 10u32 .pow (decimals) as f64;
  (num * r) .round() / r}

/// Allows to sort by float, but panics if there's a NaN or infinity
#[derive(Clone, Copy, Debug, PartialOrd, PartialEq)]
pub struct OrdFloat (pub f64);
impl Eq for OrdFloat {}
impl Ord for OrdFloat {
  fn cmp (&self, other: &Self) -> std::cmp::Ordering {
    // cf. https://doc.rust-lang.org/nightly/std/primitive.f64.html#method.total_cmp
    self.0.partial_cmp (&other.0) .expect ("!partial_cmp")}}
use std::hash::{Hash, Hasher};
impl Hash for OrdFloat {
  fn hash<H: Hasher> (&self, state: &mut H) {
    self.0.to_bits().hash (state)}}
impl std::fmt::Display for OrdFloat {
  fn fmt (&self, fm: &mut std::fmt::Formatter) -> std::fmt::Result {
    self.0.fmt (fm)}}

/// Allows to sort by float, but panics if there's a NaN or infinity
#[derive(Clone, Copy, Debug, PartialOrd, PartialEq)]
pub struct OrdF32 (pub f32);
impl Eq for OrdF32 {}
impl Ord for OrdF32 {
  fn cmp (&self, other: &Self) -> std::cmp::Ordering {
    // cf. https://doc.rust-lang.org/nightly/std/primitive.f64.html#method.total_cmp
    self.0.partial_cmp (&other.0) .expect ("!partial_cmp")}}
impl Hash for OrdF32 {
  fn hash<H: Hasher> (&self, state: &mut H) {
    self.0.to_bits().hash (state)}}
impl std::fmt::Display for OrdF32 {
  fn fmt (&self, fm: &mut std::fmt::Formatter) -> std::fmt::Result {
    self.0.fmt (fm)}}
