use core::mem::MaybeUninit;
use crate::fail;
use crate::re::Re;
use fomat_macros::{fomat, pintln};
use memchr::{memchr, memrchr};
use memmap2::{Mmap, MmapOptions, MmapMut};
use std::fs;
use std::io::Write;
use std::path::Path;
use std::str::from_utf8_unchecked;

/// Grok long lines with `memchr`. Consider using
/// [slice::Split](https://doc.rust-lang.org/nightly/std/slice/struct.Split.html)
/// when the lines are short.
/// 
/// Skips blanks.
pub struct LinesIt<'a> {
  pub lines: &'a [u8],
  pub head: usize,
  pub tail: usize}

impl<'a> LinesIt<'a> {
  pub fn new (lines: &'a [u8]) -> LinesIt<'a> {
    let (mut head, mut tail) = (0, lines.len());

    loop {
      if tail <= head {break}
      if lines[head] == b'\n' {head += 1; continue}
      break}

    loop {
      if tail <= head {break}
      if lines[tail-1] == b'\n' {tail -= 1; continue}
      break}

    LinesIt {lines, head, tail}}

  /// seek to a line at the given byte `pos`ition
  pub fn heads_up (lines: &'a [u8], pos: usize) -> LinesIt<'a> {
    let len = lines.len();
    if len < pos {
      LinesIt {lines, head: len, tail: len}
    } else {
      LinesIt {lines,
        head: memrchr (b'\n', &lines[..pos]) .unwrap_or_default(),
        tail: len}}}}

impl<'a> Iterator for LinesIt<'a> {
  type Item = &'a [u8];
  fn next (&mut self) -> Option<Self::Item> {
    loop {
      if self.tail <= self.head {return None}
      if self.lines[self.head] == b'\n' {self.head += 1; continue}
      break}
    if let Some (mut lf) = memchr (b'\n', &self.lines[self.head .. self.tail]) {
      lf += self.head;
      let line = &self.lines[self.head .. lf];
      self.head = lf + 1;
      Some (line)
    } else {
      let line = &self.lines[self.head .. self.tail];
      self.head = self.tail;
      Some (line)}}}

impl<'a> DoubleEndedIterator for LinesIt<'a> {
  fn next_back (&mut self) -> Option<Self::Item> {
    loop {
      if self.tail <= self.head {return None}
      if self.lines[self.tail-1] == b'\n' {self.tail -= 1; continue}
      break}
    if let Some (mut lf) = memrchr (b'\n', &self.lines[self.head .. self.tail]) {
      lf += self.head;
      let line = &self.lines[lf + 1 .. self.tail];
      self.tail = lf;
      Some (line)
    } else {
      let line = &self.lines[self.head .. self.tail];
      self.tail = self.head;
      Some (line)}}}

/// Unlocks on Drop
#[cfg(not(windows))]
pub struct Lock {fd: i32}

/// Unlocks on Drop
#[cfg(windows)]
pub struct Lock {handle: std::os::windows::io::RawHandle}

unsafe impl Send for Lock {}
unsafe impl Sync for Lock {}

/// try to lock the file, nonblocking
#[cfg(windows)]
pub fn lock (file: &fs::File, ex: bool) -> Result<Lock, u32> {
  // https://docs.microsoft.com/en-us/windows/win32/api/fileapi/nf-fileapi-lockfileex
  // https://docs.microsoft.com/en-us/windows/win32/fileio/locking-and-unlocking-byte-ranges-in-files
  // https://github.com/danburkert/fs2-rs/blob/9a340454a8292df025de368fc4b310bb736f382f/src/windows.rs#L108
  use std::os::windows::io::AsRawHandle;
  use winapi::um::errhandlingapi::GetLastError;
  use winapi::um::fileapi::LockFileEx;
  use winapi::um::minwinbase::{LOCKFILE_EXCLUSIVE_LOCK, LOCKFILE_FAIL_IMMEDIATELY};
  let mut flags = LOCKFILE_FAIL_IMMEDIATELY;
  if ex {flags |= LOCKFILE_EXCLUSIVE_LOCK}
  unsafe {
    let mut overlapped = MaybeUninit::zeroed().assume_init();
    let handle = file.as_raw_handle();
    let rc = LockFileEx (handle, flags, 0, 0, 0, &mut overlapped);
    if rc == 0 {
      // https://docs.microsoft.com/en-us/windows/win32/api/errhandlingapi/nf-errhandlingapi-getlasterror
      // https://docs.microsoft.com/en-us/windows/win32/debug/system-error-codes--0-499-
      Err (match GetLastError() {0 => 33, errno => errno})
    } else {Ok (Lock {handle})}}}

impl Drop for Lock {
  #[cfg(windows)]
  fn drop (&mut self) {
    use winapi::um::errhandlingapi::GetLastError;
    use winapi::um::fileapi::UnlockFileEx;
    unsafe {
      let mut overlapped = MaybeUninit::zeroed().assume_init();
      let rc = UnlockFileEx (self.handle, 0, 0, 0, &mut overlapped);
      if rc == 0 {}}}

  #[cfg(not(windows))]
  fn drop (&mut self) {
    unsafe {
      let rc = libc::flock (self.fd, libc::LOCK_UN);
      //println! ("lines] Lock::drop] {:?}; LOCK_UN rc = {}", std::thread::current().id(), rc);
      if rc == -1 {let _errno = *libc::__errno_location();}}}}

/// try to lock the file, nonblocking
#[cfg(not(windows))]
pub fn lock (file: &fs::File, ex: bool) -> Result<Lock, u32> {
  // https://linux.die.net/man/2/flock

  // To visually verify the lock:
  // 
  //     gstuff::cmd ("lsof days.csv")?;
  // 
  //     $ lsof days.csv
  //     COMMAND    PID      USER   FD   TYPE DEVICE SIZE/OFF      NODE NAME
  //     python  582669 perpetual   14rR  REG    8,4   455331 147590907 days.csv
  // 
  // https://man7.org/linux/man-pages/man8/lsof.8.html “R for a read lock on the entire file”

  use std::os::unix::io::AsRawFd;
  let mut flags = libc::LOCK_NB;
  if ex {flags |= libc::LOCK_EX} else {flags |= libc::LOCK_SH}
  unsafe {
    let fd = file.as_raw_fd();
    let rc = libc::flock (fd, flags);
    // https://man7.org/linux/man-pages/man3/errno.3.html
    if rc == -1 {Err (*libc::__errno_location() as u32)}
    else {Ok (Lock {fd})}}}

/// File, lock and memory
pub struct LockAndLoad {
  pub header: &'static [u8],
  pub lock: Lock,
  pub mmap: Mmap,
  pub file: fs::File}

impl LockAndLoad {
  /// lock and mmap the `file`, check if the `header` matches
  pub fn open (path: &dyn AsRef<Path>, ex: bool, header: &'static [u8]) -> Re<LockAndLoad> {
    let mut oop = fs::OpenOptions::new();
    oop.read (true);
    if ex {oop.write (true) .create (true);}
    let mut file = oop.open (path.as_ref())?;

    let lock = lock (&file, ex)?;

    let mut mmap = unsafe {MmapOptions::new().map (&file)?};
    if !header.is_empty() {
      if ex && mmap.is_empty() {
        file.write_all (header)?;
        mmap = unsafe {MmapOptions::new().map (&file)?}}
      if mmap.len() < header.len() || &mmap[..header.len()] != header {
        fail! ([path.as_ref()] ": unexpected header")}}

    Re::Ok (LockAndLoad {header, lock, mmap, file})}

  /// mmap exclusive
  pub fn ex (path: &dyn AsRef<Path>, header: &'static [u8]) -> Re<LockAndLoad> {
    LockAndLoad::open (path, true, header)}

  /// mmap shared
  pub fn rd (path: &dyn AsRef<Path>, header: &'static [u8]) -> Re<LockAndLoad> {
    LockAndLoad::open (path, false, header)}

  /// payload past the `header`
  pub fn bulk (&self) -> &[u8] {
    &self.mmap[self.header.len()..]}

  /// split `bulk` into lines
  pub fn lines (&self) -> impl Iterator<Item=&[u8]> {
    self.bulk().split (|ch| *ch == b'\n') .filter (|l| !l.is_empty())}

  /// iterate with `memchr`
  pub fn iter (&self) -> LinesIt {
    let bulk = self.bulk();
    LinesIt {lines: bulk, head: 0, tail: bulk.len()}}

  /// seek to a line at the given byte `pos`ition
  pub fn heads_up (&self, pos: usize) -> LinesIt {
    LinesIt::heads_up (self.bulk(), pos)}}

/// escape 1, 9 (tab), 10 (lf), 13 (cr), 34 (double quote)
/// 
/// 0 is not escaped, as it it used in binary numbers a lot.
/// 
/// NB: Some CSV viewers have a problem recognizing that the tab is used as the separator.
pub fn csesct<P> (fr: &[u8], mut push: P) where P: FnMut (u8) {
  for &ch in fr.iter() {
    if ch == 1 {push (1); push (1)}
    else if ch == 9 {push (1); push (7)}
    else if ch == 10 {push (1); push (3)}
    else if ch == 13 {push (1); push (4)}
    else if ch == 34 {push (1); push (5)}
    else {push (ch)}}}

/// escape 1, 10 (lf), 13 (cr), 34 (double quote) and 44 (comma)
/// 
/// 0 is not escaped, as it it used a lot in binary numbers.
pub fn csesc0<P> (fr: &[u8], mut push: P) where P: FnMut (u8) {
  for &ch in fr.iter() {
    if ch == 1 {push (1); push (1)}
    else if ch == 10 {push (1); push (3)}
    else if ch == 13 {push (1); push (4)}
    else if ch == 34 {push (1); push (5)}
    else if ch == 44 {push (1); push (6)}
    else {push (ch)}}}

/// escape 1, 0, 10 (lf), 13 (cr), 34 (double quote) and 44 (comma)
pub fn csesc<P> (fr: &[u8], mut push: P) where P: FnMut (u8) {
  for &ch in fr.iter() {
    if ch == 1 {push (1); push (1)}
    else if ch ==  0 {push (1); push (2)}
    else if ch == 10 {push (1); push (3)}
    else if ch == 13 {push (1); push (4)}
    else if ch == 34 {push (1); push (5)}
    else if ch == 44 {push (1); push (6)}
    else {push (ch)}}}

pub fn csunesc<P> (fr: &[u8], mut push: P) where P: FnMut (u8) {
  let len = fr.len();
  let mut ix = 0;
  loop {
    if ix == len {break}
    let code = fr[ix];
    ix += 1;
    if code == 1 && ix != len {
      let esc = fr[ix];
      ix += 1;
      if esc == 1 {push (1)}
      else if esc == 2 {push (0)}
      else if esc == 3 {push (10)}
      else if esc == 4 {push (13)}
      else if esc == 5 {push (34)}
      else if esc == 6 {push (44)}
      else if esc == 7 {push (9)}
    } else {push (code)}}}

#[cfg(all(test, feature = "nightly"))] mod test {
  extern crate test;

  use fomat_macros::pintln;
  use super::*;

  const JSON_LINES: &'static str = concat! (
    r#"{"foo": 1}"#, '\n',
    r#"{"bar": 2}"#, '\n');

  const CSV: &'static str = concat! (
    "foo,bar\n",
    "foo,1\n",
    "\n\n",  // blank lines
    "bar,2");  // no LF at the end

  #[test] fn back() {
    let mut it = LinesIt::new (JSON_LINES.as_bytes());
    assert_eq! (it.next_back().unwrap(), br#"{"bar": 2}"#);
    assert_eq! (it.next_back().unwrap(), br#"{"foo": 1}"#);
    assert_eq! (it.next_back(), None);
    assert_eq! (it.next(), None);

    it = LinesIt::new (CSV.as_bytes());
    assert_eq! (it.next_back().unwrap(), b"bar,2");
    assert_eq! (it.next_back().unwrap(), b"foo,1");
    assert_eq! (it.next_back().unwrap(), b"foo,bar");
    assert_eq! (it.next_back(), None);
    assert_eq! (it.next(), None);}

  #[test] fn forward() {
    let mut it = LinesIt::new (JSON_LINES.as_bytes());
    assert_eq! (it.next().unwrap(), br#"{"foo": 1}"#);
    assert_eq! (it.next().unwrap(), br#"{"bar": 2}"#);
    assert_eq! (it.next(), None);
    assert_eq! (it.next_back(), None);

    it = LinesIt::new (CSV.as_bytes());
    assert_eq! (it.next().unwrap(), b"foo,bar");
    assert_eq! (it.next().unwrap(), b"foo,1");
    assert_eq! (it.next().unwrap(), b"bar,2");
    assert_eq! (it.next(), None);
    assert_eq! (it.next_back(), None)}

  #[test] fn meet() {
    let mut it = LinesIt::new (JSON_LINES.as_bytes());
    assert_eq! (it.next().unwrap(), br#"{"foo": 1}"#);
    assert_eq! (it.next_back().unwrap(), br#"{"bar": 2}"#);
    assert_eq! (it.next_back(), None);
    assert_eq! (it.next(), None);

    it = LinesIt::new (& CSV.as_bytes() [8..]);
    assert_eq! (it.next().unwrap(), b"foo,1");
    assert_eq! (it.next_back().unwrap(), b"bar,2");
    assert_eq! (it.next_back(), None);
    assert_eq! (it.next(), None)}

  // cargo bench --features nightly,lines lines::

  #[bench] fn seek (bm: &mut test::Bencher) {
    let mut ix = 0;
    bm.iter (|| {
      // Can seek to any byte
      let mut it = LinesIt::heads_up (CSV.as_bytes(), ix);

      let line = it.next().unwrap();
      //pintln! ([=ix] ' ' (crate::binprint (line, b'.')));
      let expected = match ix {
         0 ..=  7 => b"foo,bar" as &[u8],
         8 ..= 13 => b"foo,1",
        14 ..= 33 => b"bar,2",
        _ => unreachable!()};
      assert_eq! (line, expected);
      ix += 1;
      if it.lines.len() <= ix {ix = 0}})}}

#[cfg(feature = "sqlite")] pub mod csq {
  // cf. https://www.sqlite.org/vtab.html, https://sqlite.org/src/file?name=ext/misc/csv.c&ci=trunk

  use core::ffi::c_int;
  use core::marker::PhantomData;
  use core::str::from_utf8;
  use crate::lines::Re;
  use crate::log;
  use fomat_macros::{fomat, wite};
  use rusqlite::{vtab, Connection, Error, Result};
  use rusqlite::ffi::{sqlite3_vtab, sqlite3_vtab_cursor};
  use rusqlite::types::Value;
  use smallvec::SmallVec;
  use std::fmt::Write;
  use std::rc::Rc;
  use super::{LockAndLoad, LinesIt};

  #[repr(C)]
  pub struct CsqVTab {
    base: sqlite3_vtab,
    ll: LockAndLoad}

  #[repr(C)]
  pub struct CsvVTabCursor<'vt> {
    base: sqlite3_vtab_cursor,
    it: LinesIt<'vt>,
    cols: SmallVec<[&'vt [u8]; 8]>,
    rowid: usize,
    eof: bool,
    phantom: PhantomData<&'vt CsqVTab>}

  //impl CsvVTabCursor<'_> {
  //  fn vtab (&self) -> &CsvVTab {unsafe {&*(self.base.pVtab as *const CsvVTab)}}}

  unsafe impl vtab::VTabCursor for CsvVTabCursor<'_> {
    fn filter (&mut self, _idx_num: c_int, _idx_str: Option<&str>, _args: &vtab::Values<'_>) -> Result<()> {
      // “When initially opened, the cursor is in an undefined state.
      // The SQLite core will invoke the xFilter method on the cursor
      // prior to any attempt to position or read from the cursor.”
      self.it.head = 0;
      self.rowid = 0;
      self.eof = false;
      self.next()}

    fn next (&mut self) -> Result<()> {
      if 0 == self.rowid {  // skip header
        if self.it.next().is_none() {self.eof = true}}
      if let Some (row) = self.it.next() {
        self.cols.clear();
        for col in row.split (|ch| *ch == b',') {self.cols.push (col)}
      } else {self.eof = true}
      if self.eof {return Ok(())}
      self.rowid += 1;
      Ok(())}

    fn eof (&self) -> bool {
      self.eof}

    fn column (&self, ctx: &mut vtab::Context, col: c_int) -> Result<()> {
      if col < 0 || self.cols.len() as c_int <= col {return Err (Error::ModuleError (fomat! ("csq] " [=col])))}
      let col = self.cols[col as usize];
      if let Ok (ustr) = from_utf8 (col) {
        ctx.set_result (&ustr)
      } else {
        ctx.set_result (&col)}}

    fn rowid (&self) -> Result<i64> {
      Ok (self.rowid as i64)}}

  unsafe impl<'vtab> vtab::VTab<'vtab> for CsqVTab {
    type Aux = ();
    type Cursor = CsvVTabCursor<'vtab>;
    fn connect (db: &mut vtab::VTabConnection, _aux: Option<&()>, args: &[&[u8]]) -> Result<(String, CsqVTab)> {
      if args.len() < 4 {return Err (Error::ModuleError ("csq] !path".into()))}
      let mut ll = None;
      let argsʹ = &args[3..];
      for c_slice in argsʹ {
        let (param, value) = vtab::parameter (c_slice)?;
        match param {
          "path" => ll = Some (match LockAndLoad::rd (&value, b"") {Re::Ok (k) => k, Re::Err (err) => {
            return Err (Error::ModuleError (fomat! ("csq] " (err))))}}),
          _ => return Err (Error::ModuleError (fomat! ("csq] unrecognized " [=param])))}}
      let Some (ll) = ll else {return Err (Error::ModuleError ("csq] !path".into()))};
      let Some (hdr) = ll.lines().next() else {return Err (Error::ModuleError ("csq] !head".into()))};
      let Ok (tname) = from_utf8 (&args[2]) else {return Err (Error::ModuleError ("csq] tname!utf8".into()))};
      let tname = vtab::escape_double_quote (tname.trim());
      let mut schema = String::with_capacity (123);
      let _ = wite! (&mut schema, "CREATE TABLE \"" (tname) "\" (");
      for (col, cn) in hdr.split (|ch| *ch == b',') .zip (0..) {
        let Ok (col) = from_utf8 (col) else {return Err (Error::ModuleError ("csq] head!utf8".into()))};
        let col = vtab::escape_double_quote (col);
        let _ = wite! (&mut schema, if cn != 0 {", "} '"' (col) "\" TEXT NOT NULL");}
      schema.push_str (");");
      let vtab = CsqVTab {base: sqlite3_vtab::default(), ll};
      // https://www.sqlite.org/c3ref/c_vtab_constraint_support.html
      db.config (vtab::VTabConfig::DirectOnly)?;
      Ok ((schema, vtab))}

    /// https://www.sqlite.org/vtab.html#the_xbestindex_method
    fn best_index (&self, info: &mut vtab::IndexInfo) -> Result<()> {
      info.set_estimated_cost (1_000_000.);
      Ok(())}

    fn open (&mut self) -> Result<CsvVTabCursor<'_>> {
      Ok (CsvVTabCursor {
        base: sqlite3_vtab_cursor::default(),
        it: self.ll.iter(),
        cols: SmallVec::new(),
        rowid: 0,
        eof: false,
        phantom: PhantomData})}}

  impl vtab::CreateVTab<'_> for CsqVTab {
    const KIND: vtab::VTabKind = vtab::VTabKind::Default;}

  pub fn csq_load (db: &Connection) -> Re<()> {
    db.create_module ("csq", vtab::read_only_module::<CsqVTab>(), None)?;
    Re::Ok(())}

  pub fn csq_poc (path: &str) -> Re<()> {
    let db = Connection::open_in_memory()?;
    db.create_module ("csq", vtab::read_only_module::<CsqVTab>(), None)?;
    let sql = fomat! ("CREATE VIRTUAL TABLE vtab USING csq (path=" (path) ")");
    db.execute_batch (&sql)?;
    let schema = db.query_row ("SELECT sql FROM sqlite_schema WHERE name = 'vtab'", [], |row| row.get::<_, String> (0))?;
    log! ("schema: " (schema));
    let mut columns = 0;
    for row in db.prepare ("SELECT * FROM pragma_table_info ('vtab')")? .query_map ([], |row| {
      let cid = row.get::<_, i32> (0)?;
      let name = row.get::<_, Rc<str>> (1)?;
      let ty = row.get::<_, Rc<str>> (2)?;
      let notnull = row.get::<_, bool> (3)?;
      log! ("column " (cid) ": " [=name] ' ' [=ty] ' ' [=notnull]);
      columns += 1;
      Ok(())})? {row?}
    let rows = db.query_row ("SELECT COUNT(*) FROM vtab", [], |row| row.get::<_, i32> (0))?;
    log! ([=rows]);
    for row in db.prepare ("SELECT rowid, * FROM vtab")? .query_map ([], |row| {
      let rowid = row.get::<_, u32> (0)?;
      for col in 0..columns {
        let val = row.get::<_, Value> (1 + col)?;
        log! ((rowid) ' ' [=val])}
      Ok(())})? {row?}
    Re::Ok(())}}

#[cfg(all(test, feature = "nightly", feature = "sqlite"))] mod csq_test {
  #[test] fn no_such_file() {
    let db = rusqlite::Connection::open_in_memory().unwrap();
    super::csq::csq_load (&db) .unwrap();
    let rc = db.execute_batch ("CREATE VIRTUAL TABLE vt USING csq (path=/no/such/file)");
    assert! (rc.is_err());
    let err = format! ("{:?}", rc);
    assert! (err.contains ("csq] lines:"));
    assert! (err.contains ("(os error "))}}

#[cfg(all(test, feature = "nightly", feature = "sqlite"))] mod csq_bench {
  extern crate test;

  use std::io::Write;
  use std::rc::Rc;

  fn gen (name: &str, num: i32) {
    let mut file = std::io::BufWriter::new (std::fs::File::create (name) .unwrap());
    for i in 0..num {writeln! (&mut file, "foo,bar,{}\n", i) .unwrap()}}

  #[bench] fn csq_open (bm: &mut test::Bencher) {
    gen ("foobar1.csv", 12345);
    bm.iter (|| {
      let db = rusqlite::Connection::open_in_memory().unwrap();
      super::csq::csq_load (&db) .unwrap();
      db.execute_batch ("CREATE VIRTUAL TABLE vt USING csq (path=foobar1.csv)") .unwrap()});
    std::fs::remove_file ("foobar1.csv") .unwrap()}

  #[bench] fn csq_select_one (bm: &mut test::Bencher) {
    let db = rusqlite::Connection::open_in_memory().unwrap();
    super::csq::csq_load (&db) .unwrap();
    gen ("foobar2.csv", 12345);
    db.execute_batch ("CREATE VIRTUAL TABLE vt USING csq (path=foobar2.csv)") .unwrap();
    let mut st = db.prepare ("SELECT * FROM vt LIMIT 1") .unwrap();
    bm.iter (|| {
      assert! (st.query_row ([], |row| Ok (row.get::<_, Rc<str>> (2) .unwrap().as_ref() == "1")) .unwrap())});
    std::fs::remove_file ("foobar2.csv") .unwrap()}

  #[bench] fn csq_next (bm: &mut test::Bencher) {
    let db = rusqlite::Connection::open_in_memory().unwrap();
    super::csq::csq_load (&db) .unwrap();
    gen ("foobar3.csv", 12345);
    db.execute_batch ("CREATE VIRTUAL TABLE vt USING csq (path=foobar3.csv)") .unwrap();
    let st = Box::into_raw (Box::new (db.prepare ("SELECT * FROM vt") .unwrap()));
    let mut rows = Box::into_raw (Box::new (unsafe {(*st).query ([]) .unwrap()}));
    let mut i = 1;
    bm.iter (|| {
      if i == 0 {
        unsafe {drop (Box::from_raw (rows))};
        rows = Box::into_raw (Box::new (unsafe {(*st).query ([]) .unwrap()}));
        i += 1
      } else if i < 12345 - 1 {
        let row = unsafe {(*rows).next().unwrap().unwrap()};
        let ri = row.get::<_, Rc<str>> (2) .unwrap();
        println! ("{}", ri);
        let ri: i32 = ri.parse().unwrap();
        assert_eq! (ri, i);
        i += 1
      } else {
        i = 0}});
    unsafe {drop (Box::from_raw (st))};
    std::fs::remove_file ("foobar3.csv") .unwrap()}}
