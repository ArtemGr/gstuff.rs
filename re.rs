// https://doc.rust-lang.org/nightly/std/ops/trait.Try.html
// https://github.com/rust-lang/rfcs/blob/master/text/3058-try-trait-v2.md
// https://github.com/rust-lang/rust/issues/84277#issuecomment-905821708
// https://blog.rust-lang.org/2020/08/27/Rust-1.46.0.html#track_caller

use fomat_macros::fomat;
use std::fmt;
use std::ops::{ControlFlow, FromResidual, Try};
use std::panic::Location;
use std::process::{ExitCode, Termination};
use super::filename;

#[macro_export]
macro_rules! fail {($($args: tt)+) => (return $crate::re::Re::fail (fomat! ($($args)+)))}

/// Ok or. Shorthand for mapping `Re::Err` with `match`.
/// 
///     let full = match fun() {Re::Ok (k) => k, Re::Err (err) => Default::default()};
///     let short = oko! (fun(), err => {Default::default()});
#[macro_export]
macro_rules! oko {
  ($e: expr, $err: ident => $er: block) => {
    match $e {Re::Ok (k) => k, Re::Err ($err) => $er}}}

#[derive(Debug, PartialEq)]
#[must_use = "this `Re` may be an `Err` variant, which should be handled"]
pub enum Re<T> {Ok (T), Err (String)}

impl<T> Termination for Re<T> {
  fn report (self) -> ExitCode {
    match self {
      Re::Ok (_) => ExitCode::SUCCESS,
      Re::Err (err) => {
        eprintln! ("{}", err);
        use std::hash::{Hash, Hasher};
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        err.hash (&mut hasher);
        ExitCode::from (1 | (hasher.finish() & 0xFF) as u8)}}}}

impl<T> Try for Re<T> {
  type Output = T;
  type Residual = Re<!>;

  #[inline]
  fn from_output (c: T) -> Self {Re::Ok (c)}

  #[inline]
  fn branch (self) -> ControlFlow<Self::Residual, T> {
    match self {
      Re::Ok (c) => ControlFlow::Continue (c),
      Re::Err (e) => ControlFlow::Break (Re::Err (e))}}}

impl<T> FromResidual<Re<!>> for Re<T> {
  #[track_caller]
  fn from_residual (x: Re<!>) -> Self {
    let err = match x {Re::Ok (_) => unreachable!(), Re::Err (e) => e};
    let loc = Location::caller();
    let err = fomat! ((filename (loc.file())) ':' (loc.line()) "] " (err));
    Re::Err (err)}}

/// Allows `Re<_>` errors to chain into `Result<_, String>` errors
/// which can be useful with libraries using `Result`, `OnceCell::get_or_try_init` for example
impl<T, O> FromResidual<Re<O>> for Result<T, String> {
  #[track_caller]
  fn from_residual (x: Re<O>) -> Self {
    let err = match x {Re::Ok (_) => unreachable!(), Re::Err (e) => e};
    let loc = Location::caller();
    let err = fomat! ((filename (loc.file())) ':' (loc.line()) "] " (err));
    Result::Err (err)}}

impl<T, O, E> FromResidual<Result<O, E>> for Re<T> where E: fmt::Display {
  #[track_caller]
  fn from_residual (x: Result<O, E>) -> Self {
    let err = match x {Result::Ok (_) => unreachable!(), Result::Err (e) => e};
    let loc = Location::caller();
    let err = fomat! ((filename (loc.file())) ':' (loc.line()) "] " (err));
    Re::Err (err)}}

impl<T, O> FromResidual<Option<O>> for Re<T> {
  #[track_caller]
  fn from_residual (_: Option<O>) -> Self {
    let loc = Location::caller();
    let err = fomat! ((filename (loc.file())) ':' (loc.line()) "] Option is None");
    Re::Err (err)}}

impl<T> Re<T> {
  #[track_caller]
  pub fn fail<E: fmt::Display> (emsg: E) -> Re<T> {
    let loc = Location::caller();
    let err = fomat! ((filename (loc.file())) ':' (loc.line()) "] " (emsg));
    Re::Err (err)}

  #[inline]
  pub fn is_ok (self) -> bool {
    match self {Re::Ok (_) => true, _ => false}}

  #[inline]
  pub fn err (self) -> Option<String> {
    match self {Re::Ok (_) => None, Re::Err (e) => Some (e)}}

  #[inline]
  #[track_caller]
  pub fn expect (self, msg: &str) -> T {
    match self {Re::Ok (k) => k, Re::Err (err) => panic! ("{}: {:?}", msg, err)}}

  #[inline]
  #[track_caller]
  pub fn unwrap (self) -> T {
    match self {Re::Ok (k) => k, Re::Err (err) => panic! ("called `Re::unwrap()` on an `Err` value: {:?}", err)}}

  #[inline]
  pub fn unwrap_or (self, default: T) -> T {
    match self {Re::Ok (k) => k, Re::Err (_) => default}}

  #[inline]
  pub fn map_err<F, O> (self, op: O) -> Result<T, F> where O: FnOnce (String) -> F {
    match self {Re::Ok (k) => Ok (k), Re::Err (err) => Err (op (err))}}

  #[inline]
  pub fn map<U, F: FnOnce (T) -> U> (self, op: F) -> Re<U> {
    match self {Re::Ok (k) => Re::Ok (op (k)), Re::Err (e) => Re::Err (e)}}}

#[cfg(all(test, feature = "nightly"))] mod test {
  extern crate test;

  use super::*;

  #[test] fn opt() {
    fn foo() -> Re<()> {
      let bar: Option<String> = None;
      bar?;
      Re::Ok(())}
    assert_eq! (foo(), Re::Err ("re:127] Option is None".into()));
    //assert_eq! (foo().report(), 521090)
  }

  #[test] fn re2result() {
    fn foo() -> Result<(), String> {
      let bar: Re<()> = Re::fail ("ups");
      bar?;
      Result::Ok(())}
    assert_eq! (foo(), Result::Err ("re:136] re:135] ups".into()));
    // #![feature(process_exitcode_internals)]
    //assert_eq! (foo().report().to_i32(), 1)
  }

  // cargo bench --features nightly,re

  fn foobar (succ: bool) -> Re<bool> {
    if test::black_box (succ) {Re::Ok (true)} else {Re::fail ("!succ")}}

  fn bang (succ: bool) -> Re<()> {
    let b = test::black_box (foobar (succ)?);
    assert_eq! (true, b);
    Re::Ok(())}

  #[bench] fn err (bm: &mut test::Bencher) {
    bm.iter (|| {
      let e = bang (false) .err().unwrap();
      assert! (e.starts_with ("re:"));
      assert! (e.ends_with ("] !succ"))})}

  #[bench] fn ok (bm: &mut test::Bencher) {
    bm.iter (|| {bang (true) .expect ("!bang")})}}
