use num_bigint::{BigInt, BigUint};
use num_traits::cast::ToPrimitive;
use num_traits::identities::Zero;
use num_traits::sign::Signed;
use smallvec::{Array, SmallVec};
use std::fmt;
use std::str::from_utf8_unchecked;

/// Prints BigInt in Base62
pub struct Bi62<'a> (pub &'a BigInt);
impl<'a> fmt::Display for Bi62<'a> {
  fn fmt (&self, ft: &mut fmt::Formatter) -> fmt::Result {
    let mut buf: SmallVec<[u8; 32]> = SmallVec::new();
    if let Err (_) = base62enc (self.0, &mut buf) {return Err (fmt::Error)}
    ft.write_str (unsafe {from_utf8_unchecked (&buf)})}}

/// Prints u64 in Base62
pub struct U62 (pub u64);
impl fmt::Display for U62 {
  fn fmt (&self, ft: &mut fmt::Formatter) -> fmt::Result {
    let mut buf: SmallVec<[u8; 32]> = SmallVec::new();
    if let Err (_) = base62uenc (self.0, &mut buf) {return Err (fmt::Error)}
    ft.write_str (unsafe {from_utf8_unchecked (&buf)})}}

pub const BASE62ALPH: &[u8; 62] = b"0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";

pub fn base62uenc<A: Array<Item=u8>> (mut ui: u64, sv: &mut SmallVec<A>) -> Result<(), String> {
  let start = sv.len();

  loop {
    sv.push (BASE62ALPH[(ui % 62) as usize]);
    ui /= 62; if ui == 0 {break}}

  let end = sv.len();
  &sv[start..end].reverse();
  Ok(())}

pub fn base62enc<A: Array<Item=u8>> (bi: &BigInt, sv: &mut SmallVec<A>) -> Result<(), String> {
  // cf. https://github.com/kryptco/base62.rs

  if let Some (u64v) = bi.to_u64() {return base62uenc (u64v, sv)}

  let mut bu = if bi.is_negative() {
    sv.push (b'-');
    bi.abs().to_biguint()
  } else {
    bi.to_biguint()
  }.unwrap();

  let start = sv.len();

  let base: BigUint = 62u32.into();
  loop {
    sv.push (BASE62ALPH[(&bu % &base).to_usize().unwrap()]);
    bu /= &base; if bu.is_zero() {break}}

  let end = sv.len();
  &sv[start..end].reverse();
  Ok(())}

/// Decode a base62 number
pub fn base62udec (bv: &[u8]) -> Result<u64, String> {
  let mut uv = 0;
  for &ch in bv.iter() {
    let v = if ch >= b'0' && ch <= b'9' {
      ch - b'0'
    } else if ch >= b'A' && ch <= b'Z' {
      ch - b'A' + 10
    } else if ch >= b'a' && ch <= b'z' {
      ch - b'a' + 36
    } else {
      return ERR! ("!base62: {}", ch)};
    uv = uv * 62 + v as u64}
  Ok (uv)}

#[cfg(all(test, feature = "nightly"))] mod test {
  extern crate test;

  use num_bigint::BigInt;
  use smallvec::SmallVec;
  use super::*;

  #[test] fn base62encᵗ() {
    // cf. https://www.dcode.fr/base-n-convert

    let mut buf: SmallVec<[u8; 32]> = SmallVec::new();
    base62enc (&0.into(), &mut buf) .unwrap();
    assert! (&buf[..] == b"0");

    buf.clear();
    base62enc (&1.into(), &mut buf) .unwrap();
    assert! (&buf[..] == b"1");

    buf.clear();
    base62enc (&10.into(), &mut buf) .unwrap();
    assert! (&buf[..] == b"A");

    buf.clear();
    base62enc (&61.into(), &mut buf) .unwrap();
    assert! (&buf[..] == b"z");

    buf.clear();
    base62enc (&62.into(), &mut buf) .unwrap();
    assert! (&buf[..] == b"10");

    buf.clear();
    base62enc (&63.into(), &mut buf) .unwrap();
    assert! (&buf[..] == b"11");

    buf.clear();
    base62enc (&123.into(), &mut buf) .unwrap();
    assert! (&buf[..] == b"1z");

    buf.clear();
    base62enc (&124.into(), &mut buf) .unwrap();
    assert! (&buf[..] == b"20");

    buf.clear();
    base62enc (&999999999.into(), &mut buf) .unwrap();
    assert! (&buf[..] == b"15ftgF");

    assert! (format! ("{}", Bi62 (&999999999.into())) == "15ftgF");

    assert! (format! ("{}", Bi62 (&(-1).into())) == "-1");
    assert! (format! ("{}", Bi62 (&(-123).into())) == "-1z");
    assert! (format! ("{}", Bi62 (&(-124).into())) == "-20");
    assert! (format! ("{}", Bi62 (&(-999999999).into())) == "-15ftgF")}

  // RUSTFLAGS=-Ctarget-cpu=native cargo bench

  #[bench] fn base62uencᵇ (bm: &mut test::Bencher) {
    let mut buf: SmallVec<[u8; 32]> = SmallVec::new();
    bm.iter (|| {
      buf.clear();
      base62uenc (999999999, &mut buf) .unwrap()});
    assert! (&buf[..] == b"15ftgF");
    assert_eq! (base62udec (b"15ftgF"), Ok (999999999))}

  #[bench] fn base62encᵇ (bm: &mut test::Bencher) {
    let mut buf: SmallVec<[u8; 32]> = SmallVec::new();
    let bi: BigInt = 999999999.into();
    bm.iter (|| {
      buf.clear();
      base62enc (&bi, &mut buf) .unwrap()});
    assert! (&buf[..] == b"15ftgF")}

  #[bench] fn base36encᵇ (bm: &mut test::Bencher) {
    let bi: BigInt = 999999999.into();
    let mut buf = String::new();
    bm.iter (|| {
      buf = bi.to_str_radix (36);
      test::black_box (&buf);});
    assert! (buf == "gjdgxr")}
}
