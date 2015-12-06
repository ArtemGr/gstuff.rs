/// Shortcut to path->filename conversion.
///
/// Returns the unchanged `path` if there is a character encoding error or something.
pub fn filename<'a> (path: &'a str) -> &'a str {
  match Path::new (path) .file_name() {
    Some (filename) => match filename.to_str() {
      Some (fstr) => if fstr.ends_with (".rs") {&fstr[0 .. fstr.len() - 3]} else {fstr},
      None => path},
    None => path}}

// A trick to use the `try_s` macro from both outside and inside the crate.
mod glim_util {pub fn filename<'a> (path: &'a str) -> &'a str {::filename (path)}}

/// Returns on error, converting the `Err` value to `String` and prepending the current location.
///
/// cf. http://www.reddit.com/r/rust/comments/29wwzw/error_handling_and_result_types/cipcm9a
#[macro_export] macro_rules! try_s {
  ($e: expr) => {match $e {Ok (ok) => ok, Err (err) => {return Err (format! ("{}:{}] {}", ::glim_util::filename (file!()), line!(), err));}}}}

// Like `try_s`, but takes a reference.
#[macro_export] macro_rules! try_sp {
  ($e: expr) => {match $e {&Ok (ref ok) => ok,
    &Err (ref err) => {return Err (format! ("{}:{}] {:?}", ::glim_util::filename (file!()), line!(), err));}}}}

/// Returns a `Err(String)`, prepending the current location (file name and line number) to the string.
///
/// Examples: `ERR! ("too bad")`; `ERR! ("{}", foo)`;
#[macro_export] macro_rules! ERR {
  ($format: expr, $($args: tt)+) => {Err (format! (concat! ("{}:{}] ", $format), ::glim_util::filename (file!()), line!(), $($args)+))};
  ($format: expr) => {Err (format! (concat! ("{}:{}] ", $format), ::glim_util::filename (file!()), line!()))}}

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
///         write! (foobar, "foo") .unwrap();
///         write! (foobar, "bar") .unwrap();
///     });
///
/// Alternatives: https://crates.io/crates/string-wrapper; https://crates.io/crates/stack.
#[macro_export] macro_rules! gstring {($array: ident, $code: block) => {{
  let end = {
    let mut $array = ::std::io::Cursor::new (&mut $array[..]);
    let $array = &mut $array;
    $code;
    $array.position() as usize};
  unsafe {::std::str::from_utf8_unchecked (&$array[0..end])}}}}
