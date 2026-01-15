use smallvec::SmallVec;
use std::fmt;
use std::io::{self, Write};
use std::str::from_utf8_unchecked;

pub struct Base91Tables {
  pub alphabet: &'static [u8],
  /// Maps an ASCII character to its `alphabet` offset:
  /// b'A' to 0, b'B' to 1, b'C' to 2.
  pub decoding_table: [i8; 256]}

const BASE: usize = 91;
const UNDEFINED: i32 = -1;

impl Base91Tables {
  pub const fn new (alphabet: &'static [u8]) -> Base91Tables {
    if alphabet.len() != BASE {panic! ("Wrong alphabet length")}
    let mut decoding_table: [i8; 256] = [UNDEFINED as i8; 256];
    let mut ofs = 0;
    loop {
      let ch = alphabet[ofs] as usize;
      decoding_table[ch] = ofs as i8;
      ofs += 1;
      if ofs == BASE {break}}
    Base91Tables {alphabet, decoding_table}}

  pub fn encode<P> (&'static self, payload: &[u8], mut push: P) where P: FnMut(u8) {
    let mut ebq: usize = 0;
    let mut en: u8 = 0;

    for &ch in payload {
      ebq |= (ch as usize) << en as usize;
      en += 8;
      if en > 13 {
        let mut ev = ebq & 8191;

        if ev > 88 {
          ebq >>= 13;
          en -= 13;
        } else {
          ev = ebq & 16383;
          ebq >>= 14;
          en -= 14}

        push (self.alphabet[ev % BASE]);
        push (self.alphabet[ev / BASE])}}

    if en > 0 {
      push (self.alphabet[ebq % BASE]);
      if en > 7 || ebq > 90 {
        push (self.alphabet[ebq / BASE])}}}

  pub fn decode<P> (&self, payload: &[u8], mut push: P) -> Result<(), String> where P: FnMut(u8) {
    let mut dbq = 0;
    let mut dn = 0;
    let mut dv = UNDEFINED;

    for ix in 0 .. payload.len() {
      let ch = payload[ix];
      let ofs = self.decoding_table[ch as usize] as i32;
      if ofs == UNDEFINED {return ERR! ("Not in alphabet: {}", ch)}
      assert_ne! (ofs, UNDEFINED);
      if dv == UNDEFINED {
        dv = ofs
      } else {
        dv += ofs * BASE as i32;
        dbq |= dv << dn;
        dn += if (dv & 8191) > 88 {13} else {14};
        loop {
          push (dbq as u8);
          dbq >>= 8;
          dn -= 8;
          if dn < 8 {break}}
        dv = UNDEFINED}}

    if dv != UNDEFINED {push ((dbq | dv << dn) as u8)}
    Ok(())}}

pub const BASE91NORM: Base91Tables = Base91Tables::new (
  b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789!#$%&()*+,./:;<=>?@[]^_`{|}~\"");

/// JSON-friendly version of Base91: double-quote (" 0x22) replaced with apostrophe (' 0x27)
pub const BASE91JS: Base91Tables = Base91Tables::new (
  b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789!#$%&()*+,./:;<=>?@[]^_`{|}~'");

/// Can be used with `fmt` to print the wrapped `payload` in Base91
pub struct Base91Display<'a> {
  pub tables: &'static Base91Tables,
  pub payload: &'a [u8]}

impl<'a> fmt::Debug for Base91Display<'a> {
  fn fmt (&self, ft: &mut fmt::Formatter) -> fmt::Result {
    fmt::Display::fmt (&self, ft)}}

impl<'a> fmt::Display for Base91Display<'a> {
  fn fmt (&self, ft: &mut fmt::Formatter) -> fmt::Result {
    let mut buf = SmallVec::<[u8; 256]>::new();
    self.tables.encode (self.payload, |ch| buf.push (ch));
    ft.write_str (unsafe {from_utf8_unchecked (&buf[..])})}}

/// Streaming Base91 encoder
pub struct Base91Output<'a, 'b> {
  pub tables: &'a Base91Tables,
  pub wr: &'b mut dyn Write,
  ebq: usize,
  en: u8}

impl<'a, 'b> Base91Output<'a, 'b> {
  pub fn new (tables: &'a Base91Tables, wr: &'b mut dyn Write) -> Base91Output<'a, 'b> {
    Base91Output {tables, wr, ebq: 0, en: 0}}}

impl<'a, 'b> Write for Base91Output<'a, 'b> {
  fn write (&mut self, buf: &[u8]) -> io::Result<usize> {
    for &ch in buf {
      self.ebq |= (ch as usize) << self.en as usize;
      self.en += 8;
      if self.en > 13 {
        let mut ev = self.ebq & 8191;

        if ev > 88 {
          self.ebq >>= 13;
          self.en -= 13;
        } else {
          ev = self.ebq & 16383;
          self.ebq >>= 14;
          self.en -= 14}

        let alph = self.tables.alphabet;
        let pair = [alph[ev % BASE], alph[ev / BASE]];
        self.wr.write_all (&pair) ?}}
    Ok(buf.len())}

  fn flush (&mut self) -> io::Result<()> {
    if self.en > 0 {
      let mut pair: [u8; 2] = [0; 2];
      pair[0] = self.tables.alphabet[self.ebq % BASE];
      if self.en > 7 || self.ebq > 90 {
        pair[1] = self.tables.alphabet[self.ebq / BASE];
        self.wr.write_all (&pair) ?;
      } else {
        self.wr.write_all (&pair[..1]) ?}}
    Ok(())}}

pub const AVERAGE_ENCODING_RATIO: f64 = 1.2297;

pub fn capacity_hint (base91len: usize) -> usize {
  (base91len as f64 / AVERAGE_ENCODING_RATIO).ceil() as usize}

#[cfg(all(test, feature = "nightly"))] mod test {
  extern crate test;

  use super::*;

  #[test] fn base91ᵗ() {
    assert_eq! (BASE91NORM.alphabet.len(), BASE);
    assert_eq! (BASE91JS.alphabet.len(), BASE);

    let test_cases: [(&[u8], &[u8]); 5] = [
      (b"test", b"fPNKd"),
      (b"Never odd or even\n", b"_O^gp@J`7RztjblLA#_1eHA"),
      (b"May a moody baby doom a yam?\n", b"8D9Kc)=/2$WzeFui#G9Km+<{VT2u9MZil}[A"),
      (b"", b""),
      (b"a", b"GB")];
    let mut buf = SmallVec::<[u8; 256]>::new();
    for (plain, b91samp) in test_cases.iter() {
      buf.clear();
      let cap = plain.len() * 12345 / 10000 + 1;  // Example of guessing capacity per “data expansion rate” of 123.077%.
      buf.grow (cap);
      let mut b91 = Base91Output::new (&BASE91NORM, &mut buf);
      b91.write (plain) .unwrap();
      b91.flush().unwrap();
      assert_eq! (&buf[..], *b91samp);
      assert! (buf.len() <= cap);

      let mut debuf = SmallVec::<[u8; 256]>::new();
      BASE91NORM.decode (b91samp, |ch| debuf.push (ch)) .unwrap();
      assert_eq! (&debuf[..], *plain)}}

  #[bench] fn base91encᵇ (bm: &mut test::Bencher) {
    let mut buf = SmallVec::<[u8; 256]>::new();
    let payload = b"foobar; foobar; foobar; foobar; foobar; foobar; foobar; foobar; foobar; foobar";
    bm.iter (|| {
      buf.clear();
      BASE91JS.encode (test::black_box (payload), |ch| buf.push (ch));
      test::black_box (&buf[..]);});
    bm.bytes = payload.len() as u64}

  #[bench] fn base91formatᵇ (bm: &mut test::Bencher) {
    let mut buf = SmallVec::<[u8; 256]>::new();
    let payload = b"foobar; foobar; foobar; foobar; foobar; foobar; foobar; foobar; foobar; foobar";
    fn b91fmt (payload: &[u8]) -> Base91Display<'_> {Base91Display {tables: &BASE91JS, payload}}
    bm.iter (|| {
      buf.clear();
      write! (&mut buf, "{}", b91fmt (payload)) .unwrap()});
    bm.bytes = payload.len() as u64}}
