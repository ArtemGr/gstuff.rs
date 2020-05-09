use smallvec::{Array, SmallVec};
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

pub const AVERAGE_ENCODING_RATIO: f64 = 1.2297;

impl Base91Tables {
  const fn new (alphabet: &'static [u8]) -> Base91Tables {
    if alphabet.len() != BASE {panic! ("Wrong alphabet length")}
    let mut decoding_table: [i8; 256] = [UNDEFINED as i8; 256];
    let mut ofs = 0;
    loop {
      let ch = alphabet[ofs] as usize;
      decoding_table[ch] = ofs as i8;
      ofs += 1;
      if ofs == BASE {break}}
    Base91Tables {alphabet, decoding_table}}

  pub fn encode<A: Array<Item=u8>> (&'static self, payload: &[u8], sv: &mut SmallVec<A>) -> io::Result<()> {
    let mut b91o = Base91Output::new (self, sv);
    b91o.write (payload) ?;
    b91o.flush() ?;
    Ok(())}

  pub fn decode<A: Array<Item=u8>> (&self, payload: &[u8], sv: &mut SmallVec<A>) -> Result<(), String> {
    let mut dbq = 0;
    let mut dn = 0;
    let mut dv = UNDEFINED;

    sv.reserve ((payload.len() as f64 / AVERAGE_ENCODING_RATIO).ceil() as usize);
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
          sv.push (dbq as u8);
          dbq >>= 8;
          dn -= 8;
          if dn < 8 {break}}
        dv = UNDEFINED}}

    if dv != UNDEFINED {sv.push ((dbq | dv << dn) as u8)}
    Ok(())}}

pub const BASE91NORM: Base91Tables = Base91Tables::new (
  b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789!#$%&()*+,./:;<=>?@[]^_`{|}~\"");

/// JSON-friendly version of Base91: double-quote (" 0x22) replaced with apostrophe (' 0x27)
pub const BASE91JS: Base91Tables = Base91Tables::new (
  b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789!#$%&()*+,./:;<=>?@[]^_`{|}~'");

/// Can be used with `fmt` to print the wrapped `payload` in Base91
pub struct Base91Display<'a, 'b> {
  pub tables: &'a Base91Tables,
  pub payload: &'b [u8]}

impl<'a, 'b> fmt::Debug for Base91Display<'a, 'b> {
  fn fmt (&self, ft: &mut fmt::Formatter) -> fmt::Result {
    fmt::Display::fmt (&self, ft)}}

impl<'a, 'b> fmt::Display for Base91Display<'a, 'b> {
  fn fmt (&self, ft: &mut fmt::Formatter) -> fmt::Result {
    struct Ascii<'a, 'b> {ft: &'a mut fmt::Formatter<'b>}
    impl<'a, 'b> Write for Ascii<'a, 'b> {
      fn flush (&mut self) -> io::Result<()> {Ok(())}
      fn write (&mut self, buf: &[u8]) -> io::Result<usize> {
        let rc = self.ft.write_str (unsafe {from_utf8_unchecked (buf)});
        if let Err (_err) = rc {return Err (io::Error::new (io::ErrorKind::Other, "fmt::Error"))}
        Ok (buf.len())}}
    let mut ascii = Ascii {ft};
    let mut b91o = Base91Output::new (self.tables, &mut ascii);
    let rc = b91o.write (self.payload);
    if let Err (_err) = rc {return Err (fmt::Error)}
    let rc = b91o.flush();
    if let Err (_err) = rc {return Err (fmt::Error)}
    Ok(())}}

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
      let mut b91 = Base91Output::new (&BASE91NORM, &mut buf);
      b91.write (plain) .unwrap();
      b91.flush().unwrap();
      assert_eq! (&buf[..], *b91samp);

      let mut debuf = SmallVec::<[u8; 256]>::new();
      BASE91NORM.decode (b91samp, &mut debuf) .unwrap();
      assert_eq! (&debuf[..], *plain)}}

  #[bench] fn base91encᵇ (bm: &mut test::Bencher) {
    let mut buf = SmallVec::<[u8; 256]>::new();
    let payload = b"foobar; foobar; foobar; foobar; foobar; foobar; foobar; foobar; foobar; foobar";
    bm.iter (|| {
      buf.clear();
      test::black_box (BASE91JS.encode (test::black_box (payload), &mut buf)) .unwrap()});
    bm.bytes = payload.len() as u64}

  #[bench] fn base91formatᵇ (bm: &mut test::Bencher) {
    let mut buf = SmallVec::<[u8; 256]>::new();
    let payload = b"foobar; foobar; foobar; foobar; foobar; foobar; foobar; foobar; foobar; foobar";
    fn b91fmt (payload: &[u8]) -> Base91Display {Base91Display {tables: &BASE91JS, payload}}
    bm.iter (|| {
      buf.clear();
      write! (&mut buf, "{}", b91fmt (payload)) .unwrap()});
    bm.bytes = payload.len() as u64}}
