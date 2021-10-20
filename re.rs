// https://doc.rust-lang.org/nightly/std/ops/trait.Try.html
// https://github.com/rust-lang/rfcs/blob/master/text/3058-try-trait-v2.md
// https://github.com/rust-lang/rust/issues/84277#issuecomment-905821708
// https://blog.rust-lang.org/2020/08/27/Rust-1.46.0.html#track_caller

use fomat_macros::fomat;
use std::fmt;
use std::ops::{ControlFlow, FromResidual, Try};
use std::panic::Location;
use super::filename;

#[macro_export]
macro_rules! fail {($($args: tt)+) => (return $crate::re::Re::fail (fomat! ($($args)+)))}

#[derive(Debug, PartialEq)]
#[must_use = "this `Re` may be an `Err` variant, which should be handled"]
pub enum Re<T> {Ok (T), Err (String)}

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
    assert_eq! (foo(), Re::Err ("re:92] Option is None".into()))}

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
