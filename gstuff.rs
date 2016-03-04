#![feature(libc)]
extern crate libc;

use std::path::Path;
use std::str::from_utf8_unchecked;

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

// Like `try_s`, but takes a reference.
#[macro_export] macro_rules! try_sp {
  ($e: expr) => {match $e {&Ok (ref ok) => ok,
    &Err (ref err) => {return Err (format! ("{}:{}] {:?}", ::gstuff::filename (file!()), line!(), err));}}}}

/// Returns a `Err(String)`, prepending the current location (file name and line number) to the string.
///
/// Examples: `ERR! ("too bad")`; `ERR! ("{}", foo)`;
#[macro_export] macro_rules! ERR {
  ($format: expr, $($args: tt)+) => {Err (format! (concat! ("{}:{}] ", $format), ::gstuff::filename (file!()), line!(), $($args)+))};
  ($format: expr) => {Err (format! (concat! ("{}:{}] ", $format), ::gstuff::filename (file!()), line!()))}}

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

#[cfg(unix)] #[test]
fn test_hostname() {
  let mut hostname = String::new();
  with_hostname (&mut |bytes| hostname = String::from_utf8_lossy (bytes) .into_owned()) .unwrap();}
