use smallvec::{Array, SmallVec};

/// NB: Compatible with the JavaScript base62,
/// https://github.com/base62/base62.js/blob/72a89c57c7c4da4552150467967b091da9f41f7f/lib/ascii.js#L3
pub const BASE62ALPH: &[u8; 62] = b"0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ";

pub fn base62uenc<A: Array<Item=u8>> (mut ui: u64, sv: &mut SmallVec<A>) -> Result<(), String> {
  let start = sv.len();

  loop {
    sv.push (BASE62ALPH[(ui % 62) as usize]);
    ui /= 62; if ui == 0 {break}}

  let end = sv.len();
  sv[start..end].reverse();
  Ok(())}

/// Decode a base62 number, compatible with JS
pub fn base62udec (bv: &[u8]) -> Result<u64, String> {
  let mut uv = 0;
  for &ch in bv.iter() {
    let v = if ch >= b'0' && ch <= b'9' {
      ch - b'0'
    } else if ch >= b'A' && ch <= b'Z' {
      ch - b'A' + 36
    } else if ch >= b'a' && ch <= b'z' {
      ch - b'a' + 10
    } else {
      return ERR! ("!base62: {}", ch)};
    uv = uv * 62 + v as u64}
  Ok (uv)}

// cargo test --features nightly,base62j
// cargo bench --features nightly,base62j

#[cfg(all(test, feature = "nightly"))] mod test {
  extern crate test;
  use super::*;

  #[bench] fn base62uencᵇ (bm: &mut test::Bencher) {
    let mut buf: SmallVec<[u8; 32]> = SmallVec::new();
    bm.iter (|| {
      buf.clear();
      base62uenc (451488, &mut buf) .unwrap()});
    assert! (&buf[..] == b"1Ts4");
    assert_eq! (base62udec (b"1Ts4"), Ok (451488))}}
