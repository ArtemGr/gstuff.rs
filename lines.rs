#[cfg(unix)] use std::os::fd::RawFd;
use core::cell::RefCell;
use core::mem::MaybeUninit;
use crate::{fail, LinesIt};
use crate::re::Re;
use fomat_macros::{fomat, pintln};
use memchr::{memchr, memrchr};
use memmap2::{Mmap, MmapOptions, MmapMut};
use std::ffi;
use std::fs;
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::ptr::null_mut;
use std::str::from_utf8_unchecked;

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
    let fls = {
      let mut fls = MaybeUninit::<libc::flock>::zeroed();
      unsafe {let flsp = fls.as_mut_ptr();
        (*flsp).l_type = libc::F_UNLCK as libc::c_short;
        (*flsp).l_whence = libc::SEEK_SET as libc::c_short;
        fls.assume_init()}};
    let cmd = nix::fcntl::FcntlArg::F_SETLK (&fls);
    let rc = nix::fcntl::fcntl (self.fd, cmd);
    debug_assert! (rc.is_ok(), "{:?}", rc)}}

/// try to lock the file, nonblocking
#[cfg(not(windows))]
pub fn lock (file: &fs::File, ex: bool) -> Result<Lock, i32> {
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

  let fls = {
    let mut fls = MaybeUninit::<libc::flock>::zeroed();
    unsafe {let flsp = fls.as_mut_ptr();
      (*flsp).l_type = if ex {libc::F_WRLCK} else {libc::F_RDLCK} as libc::c_short;
      (*flsp).l_whence = libc::SEEK_SET as libc::c_short;
      fls.assume_init()}};
  let cmd = nix::fcntl::FcntlArg::F_SETLK (&fls);  // non-blocking
  let fd = file.as_raw_fd();
  match nix::fcntl::fcntl (fd, cmd) {
    Ok (_) => Ok (Lock {fd}),
    Err(e) => Err (e as i32)}}

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
  pub fn iter (&self) -> LinesIt<'_> {
    let bulk = self.bulk();
    LinesIt {lines: bulk, head: 0, tail: bulk.len()}}

  /// seek to a line at the given byte `pos`ition
  pub fn heads_up (&self, pos: usize) -> LinesIt<'_> {
    LinesIt::heads_up (self.bulk(), pos)}

  #[cfg(unix)]
  fn write_at (&self, buf: &[u8], offset: u64) -> io::Result<usize> {
    use std::os::unix::fs::FileExt;
    self.file.write_at (buf, offset)}

  #[cfg(windows)]
  fn write_at (&self, buf: &[u8], offset: u64) -> io::Result<usize> {
    use std::os::windows::fs::FileExt;
    self.file.seek_write (buf, offset)}

  pub fn overwrite_changed (&self, fidat: &[u8]) -> Re<(u32, u32)> {
    if self.mmap.len() < fidat.len() {self.file.set_len (fidat.len() as u64)?}
    let (mut changes, mut blocks) = (0u32, 0u32);
    let mut chain_start: Option<usize> = None;

    for off in (0..fidat.len()) .step_by (4096) {
      blocks += 1;
      let len = 4096.min (fidat.len() - off);
      let new_blk = &fidat[off..off + len];
      let old_len = len.min (self.mmap.len().saturating_sub (off));
      let old_blk = &self.mmap[off..off + old_len];

      if old_len != len || new_blk != old_blk {
        changes += 1;
        if chain_start.is_none() {chain_start = Some (off)}
      } else if let Some (start) = chain_start.take() {
        self.write_at (&fidat[start..off], start as u64)?;}}

    if let Some (start) = chain_start {
      self.write_at (&fidat[start..], start as u64)?;}

    if fidat.len() < self.mmap.len() {self.file.set_len (fidat.len() as u64)?}
    Re::Ok ((changes, blocks))}}

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

#[cfg(all(test, feature = "nightly"))] mod test_lines {
  extern crate test;

  use fomat_macros::pintln;
  use super::*;

  const JSON_LINES: &'static str = concat! (
    r#"{"foo": 1}"#, '\n',
    r#"{"bar": 2}"#, '\n');

  const CSV: &'static str = concat! (
    "foo,bar\n",  // 0..8
    "foo,1\n",  // 8..14
    "\n\n",  // 14..16, blank lines
    "bar,2");  // 16..21, no LF at the end

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

#[cfg(all(feature = "base62", feature = "base91", feature = "serde_json", feature = "indexmap", feature = "gxhash", feature = "sqlite"))]
pub mod sq {
  use core::cell::UnsafeCell;
  use core::ffi::c_void;
  use core::hint::spin_loop;
  use core::mem::{transmute, ManuallyDrop};
  use core::ptr::null;
  use core::sync::atomic::{AtomicI64, Ordering};
  use crate::{any_to_str, b2s, fail, log, ms2ics, AtI64, IniMutex, SpinA, TSafe, HOST};
  use crate::base62::{base62udec, U62};
  use crate::base91::BASE91JS;
  use crate::lines::Dir;
  use crate::re::Re;
  use crate::tpool::tpost;
  use fomat_macros::{fomat, wite};
  use indexmap::IndexMap as IndexMapB;
  use inlinable_string::{InlinableString, StringExt};
  use reffers::arc::{Strong as StrongA, Ref as RefA, RefMut as RefMutA};
  use reffers::rc1::{RefMut as RefMut1, Strong as Strong1};
  use reffers::rc2::Strong as Strong2;
  use rusqlite::{ffi as s3f, CachedStatement, Connection, Rows};
  use serde_json::{self as json, json, Value as Json};
  use smallvec::SmallVec;
  use std::collections::VecDeque;
  use std::fmt;
  use std::io::{Read, Write};
  use std::panic::{catch_unwind, AssertUnwindSafe};
  use std::path::Path;
  use std::sync::{Mutex, Condvar};
  use std::sync::atomic::{AtomicBool, AtomicI16, AtomicI32};
  use std::thread::{self, JoinHandle};
  use std::time::Duration;

  type IndexMap<K, V> = IndexMapB<K, V, gxhash::GxBuildHasher>;

  #[must_use]
  pub fn sqtune (schema: &str) -> String {fomat! (
    "PRAGMA " (schema) ".page_size = 16384;"  // Might increase WAL overhead for small updates (at least a page per update)
    "PRAGMA " (schema) ".auto_vacuum = INCREMENTAL;"  // vacuum explicitly
    "PRAGMA " (schema) ".synchronous = NORMAL;"
    "PRAGMA temp_store = MEMORY;")}

  /// Invoke after `ATTACH DATABASE`
  #[must_use]
  pub fn sqwal (schema: &str) -> String {fomat! (
    "PRAGMA " (schema) ".journal_mode = WAL;"
    "PRAGMA " (schema) ".journal_size_limit = 1048576;"  // truncate unused WAL to 1 MiB
    "PRAGMA wal_autocheckpoint = 0;")}  // checkpoints explicitly or at database close

  pub fn sqdaver (db: &Connection) -> Re<u32> {
    let s3: *mut s3f::sqlite3 = unsafe {db.handle()};
    // https://www.sqlite.org/c3ref/c_fcntl_begin_atomic_write.html#sqlitefcntldataversion
    let mut sqdaver = 0u32;
    let rc = unsafe {s3f::sqlite3_file_control (s3, null(), s3f::SQLITE_FCNTL_DATA_VERSION, &mut sqdaver as *mut u32 as *mut c_void)};
    if rc != 0 {fail! ("!sqdaver: " [rc])}
    Re::Ok (sqdaver)}

  pub fn quick_check (db: &Connection, path: Option<&dyn AsRef<Path>>) -> Re<()> {
    use std::rc::Rc;
    let mut st = db.prepare ("PRAGMA main.quick_check")?; let mut rows = st.query([])?;
    while let Some (row) = rows.next()? {
      let c0 = row.get_ref (0)? .as_str()?;
      if c0 == "ok" {continue}
      fail! (if let Some (path) = path {(path.as_ref().display()) ' '} "quick_check: " (c0))}
    Re::Ok(())}

  /// fetch `i32` at `column` from the next row, or `0` if NULL/end
  pub fn z32 (rows: &mut Rows, column: usize) -> Re<i32> {
    let Some (row) = rows.next()? else {return Re::Ok (0)};
    Re::Ok (row.get::<_, Option<i32>> (column)? .unwrap_or (0))}

  pub struct SqRows {
    rows: ManuallyDrop<UnsafeCell<Rows<'static>>>,  // pImpl to `sth`
    sth: ManuallyDrop<Strong1<CachedStatement<'static>>>,
    db: ManuallyDrop<SConn>}

  impl SqRows {
    pub fn new (rows: Rows<'static>, sth: Strong1<CachedStatement<'static>>, db: SConn) -> SqRows {SqRows {
      rows: ManuallyDrop::new (UnsafeCell::new (rows)),
      sth: ManuallyDrop::new (sth),
      db: ManuallyDrop::new (db)}}

    pub fn r<'a> (&'a self) -> &'a mut Rows<'a> {
      unsafe {transmute (&mut *self.rows.get())}}

    /// fetch text at `column` from the next row, empty if NULL/end
    pub fn is (&self, column: usize) -> Re<InlinableString> {
      let Some (row) = self.r().next()? else {return Re::Ok (InlinableString::new())};
      let s = row.get_ref (column)? .as_str()?;
      Re::Ok (InlinableString::from (s))}

    /// fetch text at `column` from the next row, empty if NULL/end
    pub fn s (&self, column: usize) -> Re<String> {
      let Some (row) = self.r().next()? else {return Re::Ok (String::new())};
      let s = row.get_ref (column)? .as_str()?;
      Re::Ok (String::from (s))}

    /// fetch `i32` at `column` from the next row, or `0` if NULL/end
    pub fn z32 (&self, column: usize) -> Re<i32> {
      let Some (row) = self.r().next()? else {return Re::Ok (0)};
      Re::Ok (row.get::<_, Option<i32>> (column)? .unwrap_or (0))}

    /// fetch `i64` at `column` from the next row, or `0` if NULL/end
    pub fn z64 (&self, column: usize) -> Re<i64> {
      let Some (row) = self.r().next()? else {return Re::Ok (0)};
      Re::Ok (row.get::<_, Option<i64>> (column)? .unwrap_or (0))}

    /// fetch `f32` at `column` from the next row, or `NAN` if NULL/end
    pub fn f32 (&self, column: usize) -> Re<f32> {
      let Some (row) = self.r().next()? else {return Re::Ok (f32::NAN)};
      Re::Ok (row.get::<_, Option<f32>> (column)? .unwrap_or (f32::NAN))}

    /// fetch `f64` at `column` from the next row, or `NAN` if NULL/end
    pub fn f64 (&self, column: usize) -> Re<f64> {
      let Some (row) = self.r().next()? else {return Re::Ok (f64::NAN)};
      Re::Ok (row.get::<_, Option<f64>> (column)? .unwrap_or (f64::NAN))}}

  impl Drop for SqRows {
    fn drop (&mut self) {unsafe {
      ManuallyDrop::drop (&mut self.rows);  // Before `sth`
      ManuallyDrop::drop (&mut self.sth);  // Before `db`
      ManuallyDrop::drop (&mut self.db)}}}

  pub fn run2rows (db: &SConn, sql: &[u8]) -> Re<SqRows> {
    let dbʹ = db.spinʳ()?;
    let mut st = RefMut1::new (dbʹ.0.prepare_cached (unsafe {core::str::from_utf8_unchecked (sql)})?);
    let rs = st.query([])?;
    Re::Ok (unsafe {SqRows::new (
      core::mem::transmute (rs),
      core::mem::transmute (st.get_strong()),
      db.clone())})}

  /// return `Rows` wrapped together with `Statement`
  /// 
  ///     let rows = sq! (db, [4 + 4], "SELECT 2 + 2, " (3 + 3) ", ?");
  ///     let (four, six, eight): (u32, u64, i32) = rows.r().next()??.try_into()?;
  ///     let (f, s, e) = if let Some (row) = rows.r().next()? {row.try_into()?} else {(0u32, 0u64, 0)};
  ///     while let Some (row) = rows.r().next()? {let (f, s, e): (u32, u64, i32) = row.try_into()?;}
  /// 
  /// with helpers, such as
  /// 
  ///     let four = sq! (db, [2 + 2], "SELECT ?1") .z32(0)?;
  /// 
  /// NB: Row is a singleton in SQLite, only use one before fetching another.
  #[macro_export] macro_rules! sq {
    ($db: expr, $params: expr, $($fq: tt)+) => {{
      use $crate::SpinA;
      let mut sql = smallvec::SmallVec::<[u8; 256]>::new();
      fomat_macros::wite! (&mut sql, $($fq)+)?;
      let dbʹ = $db.spinʷ()?;
      let mut st = reffers::rc1::RefMut::new (dbʹ.0.prepare_cached (unsafe {core::str::from_utf8_unchecked (&sql)})?);
      let rs = st.query ($params)?;
      unsafe {$crate::lines::sq::SqRows::new (
        core::mem::transmute (rs),
        core::mem::transmute (st.get_strong()),
        $db.clone())}}}}

  #[macro_export] macro_rules! se {
    ($db: expr, $params: expr, $($fq: tt)+) => {{
      use $crate::SpinA;
      let mut buf = smallvec::SmallVec::<[u8; 256]>::new();
      fomat_macros::wite! (&mut buf, $($fq)+)?;
      let dbʹ = $db.spinʷ()?;
      let mut sth = dbʹ.0.prepare_cached (unsafe {core::str::from_utf8_unchecked (&buf)})?;
      sth.execute ($params)?}};

    (e $expect: expr, $db: expr, $params: expr, $($fq: tt)+) => {{
      let expect = $expect as usize;
      let ups = se! ($db, $params, $($fq)+);
      if ups != expect {fail! ("ups " (ups) " <> " (expect) " expect")}}}}

  /// cf. “string constant” at [literal values](https://www.sqlite.org/lang_expr.html#literal_values_constants_)
  /// cf. [expanded_sql](https://docs.rs/rusqlite/latest/rusqlite/struct.Statement.html#method.expanded_sql)
  #[must_use]
  pub struct SqEsc<'a> (pub &'a str);
  impl<'a> fmt::Display for SqEsc<'a> {
    fn fmt (&self, ft: &mut fmt::Formatter<'_>) -> fmt::Result {
      use fmt::Write;
      for ch in self.0.chars() {match ch {
        '\'' => {ft.write_char ('\'')?; ft.write_char ('\'')?},
        _ => ft.write_char (ch)?}}
      fmt::Result::Ok(())}}

  pub fn run2js (db: &SConn, sql: &[u8]) -> Re<Vec<IndexMap<InlinableString, Json>>> {
    let dbʹ = db.try_get_ref()?;
    let mut st = dbʹ.0.prepare (b2s (sql))?;
    let cols = st.column_count();
    let mut cnames = Vec::with_capacity (cols);
    for cx in 0 .. cols {cnames.push (InlinableString::from (st.column_name (cx)?))}
    let mut rows = st.query([])?;
    let mut js = Vec::new();
    while let Some (row) = rows.next()? {
      let mut jr = IndexMap::default();
      for cx in 0 .. cols {
        jr.insert (cnames[cx].clone(), match row.get_ref (cx)? {
          rusqlite::types::ValueRef::Null => Json::Null,
          rusqlite::types::ValueRef::Integer (i) => Json::from (i),
          rusqlite::types::ValueRef::Real (f) => Json::from (f),
          rusqlite::types::ValueRef::Text (t) => Json::String (unsafe {String::from_utf8_unchecked (Vec::from (t))}),
          rusqlite::types::ValueRef::Blob (b) => {
            let mut sb = Vec::with_capacity (b.len() * 12345 / 10000 + 1);
            BASE91JS.encode (b, |ch| sb.push (ch));
            Json::String (unsafe {String::from_utf8_unchecked (sb)})}});}
      js.push (jr)}
    Re::Ok (js)}

  /// Should [prefer exclusive access](https://github.com/rusqlite/rusqlite/issues/342#issuecomment-592661330), `spinᵐ`,
  /// unless we're using the database from a single thread anyway.
  pub type SConn = StrongA<TSafe<rusqlite::Connection>>;
  pub fn sconn (db: Connection) -> SConn {StrongA::new (TSafe (db))}}
//dai//
#[cfg(feature = "sqlite")] pub mod csq {
  // cf. https://www.sqlite.org/vtab.html, https://sqlite.org/src/file?name=ext/misc/csv.c&ci=trunk

  use core::ffi::c_int;
  use core::marker::PhantomData;
  use core::str::from_utf8;
  use crate::lines::Re;
  use crate::{log, LinesIt};
  use fomat_macros::{fomat, wite};
  use rusqlite::{vtab, Connection, Error, Result};
  use rusqlite::ffi::{sqlite3_vtab, sqlite3_vtab_cursor};
  use rusqlite::types::Value;
  use smallvec::SmallVec;
  use std::fmt::Write;
  use std::rc::Rc;
  use super::LockAndLoad;

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
    fn filter (&mut self, _idx_num: c_int, _idx_str: Option<&str>, _args: &vtab::Filters<'_>) -> Result<()> {
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

  use crate::lines::Re;
  use scopeguard::defer;
  use std::fs;
  use std::hint::black_box;
  use std::io::Write;
  use std::rc::Rc;

  fn gen (name: &str, num: i32) {
    let mut file = std::io::BufWriter::new (fs::File::create (name) .unwrap());
    for i in 0..num {writeln! (&mut file, "foo,bar,{}", i) .unwrap()}}

  #[bench] fn lock_load_rd (bm: &mut test::Bencher) {
    #[cfg(unix)] std::env::set_current_dir ("/tmp") .unwrap();
    gen ("lock_load_rd", 12345);
    defer! {fs::remove_file ("lock_load_rd") .unwrap()}
    bm.iter (|| {
      let fl = super::LockAndLoad::rd (&"lock_load_rd", b"foo,bar,0") .unwrap();
      assert! (123456 < fl.mmap.len())})}

  #[cfg(unix)] #[test] fn lock_ex_not_rd() {
    std::env::set_current_dir ("/tmp") .unwrap();
    defer! {
      fs::remove_file ("lock_ex_not_rd") .unwrap();
      fs::remove_file ("lock_ex_not_rd.rd") .unwrap()}  // Tests the forked flag
    let _fl = super::LockAndLoad::ex (&"lock_ex_not_rd", b"") .unwrap();  // Creates and locks the file
    if unsafe {libc::fork()} == 0 {
      let Re::Err (err) = super::LockAndLoad::rd (&"lock_ex_not_rd", b"") else {panic! ("rd")};
      assert! (err.ends_with ("] 11"));  // Locked in parent
      fs::File::create ("lock_ex_not_rd.rd") .unwrap();  // flag as tested
      std::process::exit (0)
    } else {
      while !std::path::Path::new ("lock_ex_not_rd.rd") .exists() {
        std::thread::sleep (std::time::Duration::from_secs_f32 (0.123))}}}

  #[bench] fn lock_ex (bm: &mut test::Bencher) {
    #[cfg(unix)] std::env::set_current_dir ("/tmp") .unwrap();
    gen ("csq_bench-ex.csv", 12345);
    defer! {fs::remove_file ("csq_bench-ex.csv") .unwrap()}
    bm.iter (|| {
      let file = fs::OpenOptions::new().read (true) .write (true) .create (true)
        .open ("csq_bench-ex.csv") .unwrap();
      let _lock = black_box (super::lock (&file, true) .unwrap());
      #[cfg(unix)] {assert! (_lock.fd != 0)}})}

  #[cfg(all(unix, test))] fn sqrm (path: &str) {
    let _ = fs::remove_file (path);
    let _ = fs::remove_file (format! ("{}-shm", path));
    let _ = fs::remove_file (format! ("{}-wal", path));}

  /// create and lock test SQLite database at `path`
  #[cfg(all(unix, test))] fn sqlock (path: &str, ex: bool, flag: &str) {
    sqrm (path);
    let db3 = rusqlite::Connection::open (path) .unwrap();
    db3.execute_batch (&super::sq::sqtune ("main")) .unwrap();
    db3.execute_batch (&super::sq::sqwal ("main")) .unwrap();
    if ex {db3.execute_batch ("PRAGMA main.locking_mode = EXCLUSIVE") .unwrap()}
    db3.execute_batch ("CREATE TABLE t (foo, bar); INSERT INTO t VALUES (1, 2);") .unwrap();  // Locks
    fs::File::create (flag) .unwrap();
    std::thread::sleep (std::time::Duration::from_secs_f32 (2.345))}

  /// verify that `rd` fails against EXCLUSIVE
  #[cfg(unix)] #[test] fn lock_sq_rd() {
    std::env::set_current_dir ("/tmp") .unwrap();
    defer! {fs::remove_file ("lock_sq_rd.created") .unwrap(); sqrm ("lock_sq_rd.db3")}
    if unsafe {libc::fork()} == 0 {
      sqlock ("lock_sq_rd.db3", true, "lock_sq_rd.created"); std::process::exit (0)
    } else {
      while !std::path::Path::new ("lock_sq_rd.created") .exists() {
        std::thread::sleep (std::time::Duration::from_secs_f32 (0.123))}
      let Re::Err (err) = super::LockAndLoad::rd (&"lock_sq_rd.db3", b"") else {panic! ("rd")};
      assert! (err.ends_with ("] 11"))}}

  /// verify that `ex` fails against SHARED
  #[cfg(unix)] #[test] fn lock_sq_ex() {
    std::env::set_current_dir ("/tmp") .unwrap();
    defer! {fs::remove_file ("lock_sq_ex.created") .unwrap(); sqrm ("lock_sq_ex.db3")}
    if unsafe {libc::fork()} == 0 {
      sqlock ("lock_sq_ex.db3", false, "lock_sq_ex.created"); std::process::exit (0)
    } else {
      while !std::path::Path::new ("lock_sq_ex.created") .exists() {
        std::thread::sleep (std::time::Duration::from_secs_f32 (0.123))}
      let Re::Err (err) = super::LockAndLoad::ex (&"lock_sq_ex.db3", b"") else {panic! ("ex")};
      assert! (err.ends_with ("] 11"))}}

  #[bench] fn csq_open (bm: &mut test::Bencher) {
    #[cfg(unix)] std::env::set_current_dir ("/tmp") .unwrap();
    gen ("foobar1.csv", 12345);
    defer! {fs::remove_file (&"foobar1.csv") .unwrap()}
    bm.iter (|| {
      let db = rusqlite::Connection::open_in_memory().unwrap();
      super::csq::csq_load (&db) .unwrap();
      db.execute_batch ("CREATE VIRTUAL TABLE vt USING csq (path=foobar1.csv)") .unwrap()})}

  #[bench] fn csq_select_one (bm: &mut test::Bencher) {
    #[cfg(unix)] std::env::set_current_dir ("/tmp") .unwrap();
    let db = rusqlite::Connection::open_in_memory().unwrap();
    super::csq::csq_load (&db) .unwrap();
    gen ("foobar2.csv", 12345);
    defer! {fs::remove_file ("foobar2.csv") .unwrap()}
    db.execute_batch ("CREATE VIRTUAL TABLE vt USING csq (path=foobar2.csv)") .unwrap();
    let mut st = db.prepare ("SELECT * FROM vt LIMIT 1") .unwrap();
    bm.iter (|| {
      assert! (st.query_row ([], |row| Ok (row.get::<_, Rc<str>> (2) .unwrap().as_ref() == "1")) .unwrap())})}

  #[bench] fn csq_next (bm: &mut test::Bencher) {
    #[cfg(unix)] std::env::set_current_dir ("/tmp") .unwrap();
    let db = rusqlite::Connection::open_in_memory().unwrap();
    super::csq::csq_load (&db) .unwrap();
    gen ("foobar3.csv", 12345);
    defer! {fs::remove_file ("foobar3.csv") .unwrap()}
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
        let ri: i32 = ri.parse().unwrap();
        assert_eq! (ri, i);
        i += 1
      } else {
        i = 0}});
    unsafe {drop (Box::from_raw (st))}}}

pub fn crc16ccitt (mut crc: u16, ch: u8) -> u16 {
  let mut v = 0x80u16;
  for _ in 0u16..8 {
    let xor_flag = (crc & 0x8000) != 0;
    crc = crc << 1;
    if (ch as u16 & v) != 0 {crc = crc + 1}
    if xor_flag {crc = crc ^ 0x1021}
    v = v >> 1}
  crc}

/// [CRC16-CCITT](https://srecord.sourceforge.net/crc16-ccitt.html),
/// matches [CRC calculation](http://www.zorc.breitbandkatze.de/crc.html) with “Initial value: 1D0F”
pub fn crc16ccitt_aug (mut crc: u16) -> u16 {
  for _ in 0u16..16 {
    let xor_flag = (crc & 0x8000) != 0;
    crc = crc << 1;
    if xor_flag {crc = crc ^ 0x1021}}
  crc}

#[cfg(all(test, feature = "nightly"))] mod crc_bench {
  extern crate test;
  use crate::lines::{crc16ccitt, crc16ccitt_aug};
  use std::io::Write;
  use std::rc::Rc;
  use test::black_box;

  #[bench] fn crc16mb (bm: &mut test::Bencher) {
    let mut buf = [0u8; 1234];
    let mut ch = 0; for ci in 0..buf.len() {buf[ci] = ch; ch = ch.wrapping_add (1)}
    let (mut fr, mut bytes) = (0, 0);
    bm.iter (|| {
      let mut crc = 0xFFFF;
      for &ch in &buf[fr..] {crc = crc16ccitt (crc, test::black_box (ch))}
      bytes += buf.len() - fr;
      fr += 1; if 321 < fr {fr = 0}});
    bm.bytes = bytes as u64}

  #[bench] fn crc16 (bm: &mut test::Bencher) {
    bm.iter (|| {
      assert_eq! (0x1D0F, crc16ccitt_aug (black_box (0xFFFF)))})}

  #[bench] fn crc16_a (bm: &mut test::Bencher) {
    assert_eq! (0xE1B1, crc16ccitt (0xFFFF, black_box (b'A')));
    bm.iter (|| {
      let crc = crc16ccitt (0xFFFF, black_box (b'A'));
      assert_eq! (0x9479, crc16ccitt_aug (black_box (crc)))})}

  #[bench] fn crc16_123456789 (bm: &mut test::Bencher) {
    bm.iter (|| {
      let mut crc = 0xFFFF;
      for ch in b"123456789" {
        crc = crc16ccitt (crc, black_box (*ch))}
      assert_eq! (0xE5CC, crc16ccitt_aug (black_box (crc)))})}

  #[bench] fn c8_123456789 (bm: &mut test::Bencher) {
    bm.iter (|| {
      let c8 = b"123456789".iter().fold (0u8, |a, &b| black_box (a.wrapping_add (b)));
      assert_eq! (0xDD, c8)})}}

#[derive (Clone, Debug, Default)]
pub struct Stat {
  pub len: i64,
  /// Last-modified in centiseconds
  pub lmc: u64,
  pub dir: bool,
  pub link: bool}

#[cfg(unix)] pub fn fstat (fd: RawFd) -> Re<Stat> {
  let mut buf: libc::stat = unsafe {MaybeUninit::zeroed().assume_init()};
  let rc = unsafe {libc::fstat (fd, &mut buf)};
  if rc == -1 {fail! ((io::Error::last_os_error()))}
  let lmc = (buf.st_mtime as u64 * 100) + (buf.st_mtime_nsec / 10000000) as u64;
  let dir = buf.st_mode & libc::S_IFMT == libc::S_IFDIR;
  let link = buf.st_mode & libc::S_IFMT == libc::S_IFLNK;
  Re::Ok (Stat {len: buf.st_size as i64, lmc, dir, link})}

#[cfg(unix)] pub struct Dir {
  pub fd: RawFd,
  dir: RefCell<*mut libc::DIR>}

#[cfg(unix)] impl Dir {
  pub fn new (path: &dyn AsRef<Path>, flags: i8) -> Re<Dir> {
    let path = ffi::CString::new (path.as_ref().to_str()?)?;
    let mut fl = libc::O_RDONLY | libc::O_CLOEXEC | libc::O_DIRECTORY | libc::O_NOCTTY;
    // Processes lacking CAP_FOWNER cannot bypass ownership checks for O_NOATIME
    if flags & 0b1 == 0 {fl |= libc::O_NOATIME}
    // https://man7.org/linux/man-pages/man2/open.2.html
    let fd = unsafe {libc::open (path.as_ptr(), fl, 0)};
    if fd == -1 {fail! ((io::Error::last_os_error()))}
    Re::Ok (Dir {fd, dir: RefCell::new (null_mut())})}

  pub fn list (&self, cb: &mut dyn FnMut (&[u8]) -> Re<bool>) -> Re<()> {
    if self.dir.borrow().is_null() {
      // https://man7.org/linux/man-pages/man3/opendir.3.html
      let dir = unsafe {libc::fdopendir (self.fd)};
      if dir.is_null() {fail! ((io::Error::last_os_error()))}
      self.dir.replace (dir);
    } else {
      unsafe {libc::rewinddir (*self.dir.borrow())}}
    loop {
      // https://linux.die.net/man/3/readdir
      // https://pubs.opengroup.org/onlinepubs/9699919799/functions/readdir.html
      let dp = unsafe {libc::readdir (*self.dir.borrow())};
      if dp.is_null() {break}
      let name = unsafe {ffi::CStr::from_ptr ((*dp).d_name.as_ptr())};
      let name = name.to_bytes();
      if name == b"." || name == b".." {continue}
      if !cb (name)? {break}}
    Re::Ok(())}

  pub fn file (&self, name: &[u8], creat: bool, append: bool) -> Re<fs::File> {
    use std::os::fd::FromRawFd;
    let mut flags = libc::O_RDWR | libc::O_CLOEXEC | libc::O_NOCTTY | libc::O_NOATIME;
    if creat {flags |= libc::O_CREAT}
    if append {flags |= libc::O_APPEND}
    let cname = ffi::CString::new (name)?;
    // https://linux.die.net/man/2/openat
    // https://man.freebsd.org/cgi/man.cgi?query=openat
    // https://pubs.opengroup.org/onlinepubs/9699919799/functions/open.html
    let fd = unsafe {libc::openat (self.fd, cname.as_ptr(), flags, 0o0600)};
    if fd == -1 {fail! ((String::from_utf8_lossy (name)) "] " (io::Error::last_os_error()))}
    Re::Ok (unsafe {fs::File::from_raw_fd (fd)})}

  pub fn stat (&self, name: &[u8]) -> Re<Option<Stat>> {
    let cname = ffi::CString::new (name)?;
    let mut buf: libc::stat = unsafe {MaybeUninit::zeroed().assume_init()};
    // https://pubs.opengroup.org/onlinepubs/9699919799/functions/fstatat.html
    let rc = unsafe {libc::fstatat (self.fd, cname.as_ptr(), &mut buf, libc::AT_SYMLINK_NOFOLLOW)};
    if rc == -1 {
      let err = io::Error::last_os_error();
      if err.kind() == io::ErrorKind::NotFound {return Re::Ok (None)}
      fail! ((io::Error::last_os_error()))}

    // NB: `st_mtime` might be zero when a file was unpacked from a non-preserving archive
    // (seen it grow negative with a buggy Syncthing)
    let lmc = (buf.st_mtime as u64 * 100) + (buf.st_mtime_nsec / 10000000) as u64;
    let dir = buf.st_mode & libc::S_IFMT == libc::S_IFDIR;
    let link = buf.st_mode & libc::S_IFMT == libc::S_IFLNK;
    Re::Ok (Some (Stat {len: buf.st_size as i64, lmc, dir, link}))}

  /// On some filesystems, `unlink`ing during a `list` can skip,
  /// [cf.](https://stackoverflow.com/a/14454310/257568)
  pub fn unlink (&self, name: &[u8], dir: bool) -> Re<()> {
    let cname = ffi::CString::new (name)?;
    let flags = if dir {libc::AT_REMOVEDIR} else {0};
    // https://linux.die.net/man/2/unlinkat
    // https://man.freebsd.org/cgi/man.cgi?query=unlinkat
    // https://pubs.opengroup.org/onlinepubs/9699919799/functions/unlinkat.html
    let rc = unsafe {libc::unlinkat (self.fd, cname.as_ptr(), flags)};
    if rc == -1 {fail! ((io::Error::last_os_error()))}
    Re::Ok(())}}

#[cfg(unix)] impl Drop for Dir {
  fn drop (&mut self) {
    let dir = self.dir.borrow_mut();
    if dir.is_null() {
      unsafe {libc::close (self.fd);}
    } else {
      unsafe {libc::closedir (*dir);}}}}

#[cfg(not(unix))] pub struct Dir {
  _path: PathBuf}

#[cfg(not(unix))] impl Dir {
  pub fn new (path: &dyn AsRef<Path>, _flags: i8) -> Re<Dir> {
    Re::Ok (Dir {_path: path.as_ref().to_path_buf()})}

  /// `dir.list (&mut |nm| {log! ((b2s (nm))); Re::Ok (true)})?;`
  pub fn list (&self, _cb: &mut dyn FnMut (&[u8]) -> Re<bool>) -> Re<()> {
    fail! ("tbd")}

  /// Open a file in the directory.
  /// 
  /// * `creat` - Make a new file if one does not exists. O_CREAT
  /// * `append` - Seek to end before each `write`. O_APPEND
  pub fn file (&self, _name: &[u8], _creat: bool, _append: bool) -> Re<fs::File> {
    fail! ("tbd")}

  pub fn stat (&self, _name: &[u8]) -> Re<Option<Stat>> {
    fail! ("tbd")}

  /// On some filesystems, `unlink`ing during a `list` can skip,
  /// [cf.](https://stackoverflow.com/a/14454310/257568)
  pub fn unlink (&self, _name: &[u8], _dir: bool) -> Re<()> {
    fail! ("tbd")}}

unsafe impl Send for Dir {}
unsafe impl Sync for Dir {}

//⌥ synchronization is likely too specific and heavy in dependencies to be kept here,
// like when we'd use tailscale for a second port to a host, - should move the code to alib
//⌥ there are also contextual optimizations (zsync in network.md) making one-size-fits-all solution unlikely

#[cfg(feature = "sync")]
pub mod sync {
  use core::str::from_utf8;
  use crate::{fail, slurp, now_ms};
  use crate::lines::{lock, Dir, Lock};
  use crate::re::Re;
  use fast_rsync::{Signature, SignatureOptions};
  use fomat_macros::fomat;
  use indexmap::IndexMap as IndexMapB;
  use indexmap::map::Entry;
  use inlinable_string::{InlinableString, StringExt};
  use serde::{Deserialize, Serialize};
  use std::fs;
  use std::io::{self, Read, Write, Seek};
  use std::path::Path;
  use std::time::{Duration, UNIX_EPOCH};

  type IndexMap<K, V> = IndexMapB<K, V, gxhash::GxBuildHasher>;

  #[derive (Clone, Debug)]
  pub struct File {
    pub hosts: InlinableString,
    pub dir: InlinableString,
    pub name: InlinableString}

  pub fn parse_files (csv: &[u8]) -> Re<Vec<File>> {
    let mut files = Vec::new();
    for (line, lx) in csv.split (|ch| *ch == b'\n') .zip (0..) {
      if lx == 0 {if line != b"hosts,dir,name" {fail! ("!head")} continue}
      if line.is_empty() {continue}
      let (mut hosts, mut dir, mut name) = (InlinableString::new(), InlinableString::new(), InlinableString::new());
      for (col, cx) in line.split (|ch| *ch == b',') .zip (0..) {
        if cx == 0 {hosts = InlinableString::from (from_utf8 (col.into())?)
        } else if cx == 1 {dir = InlinableString::from (from_utf8 (col.into())?)
        } else if cx == 2 {name = InlinableString::from (from_utf8 (col.into())?)
        } else {fail! ([=cx])}}
      files.push (File {hosts, dir, name})}
    Re::Ok (files)}

  #[derive (Default)]
  pub struct State {
    pub files: Vec<File>,
    pub fds: IndexMap<u16, fs::File>,
    pub locks: IndexMap<u16, (Lock, u32, Vec<u8>)>,
    pub dirs: IndexMap<InlinableString, Dir>}

  #[derive (Debug, Deserialize, Serialize)]
  pub enum Req {
    RsyncProto1 {
      fx: u16,
      flen: u32,
      lm: u64,
      ofs: u32,
      sig: Vec<u8>}}

  #[derive (Debug, Deserialize, Serialize)]
  pub enum Rep {
    RsyncProto1 {
      fx: u16,
      lm: u64,
      ofs: u32,
      delta: Vec<u8>,
      dlen: u32,
      bsum: u16}}

  /// Aims to reduce the cost of frequent or periodic updates, also large append-only rotating updates.
  /// For small and infrequent updates, or directories, a different method might work.
  pub fn rsync_pull (reqs: &mut Vec<Req>, hostname: &str, state: &mut State, name: &str, tail: i32, block: u16, hash: u8) -> Re<()> {
    //⌥ first request should compare length and time,
    //  and only when they differ should we lock the file, put length and time in `state`,
    //  compute the Signature and request rsync update
    //⌥ should only lock the file when we have found it to be different by size/time,
    //  and making a second request with the Signature,
    //  in order not to lock during long poll
    //  (and Signature requests should always be served immediately)
    //⌥ consider caching the actual bytes of the file in the State,
    //  so that even if someone writes while we wait, we would restore a pristine copy
    //⌥ consider making the tail mode a norm: build the Signature from a given offset,
    //  0 for whole file
    let (file, fx) = {let mut it = state.files.iter().zip (0u16..); 'file: loop {
      let Some ((file, fx)) = it.next() else {fail! ("!file")};
      if file.name != name {continue}
      for host in file.hosts.split ('&') {
        if host == hostname {break 'file (file, fx)}}}};

    let fd = match state.fds.entry (fx) {
      Entry::Vacant (ve) => {
        let path = Path::new (&file.dir[..]) .join (name);
        ve.insert (fs::OpenOptions::new() .read (true) .write (true) .create (true) .open (&path)?)},
      Entry::Occupied (oe) => oe.into_mut()};

    let (_lock, ofs, bytes) = match state.locks.entry (fx) {
      Entry::Vacant (ve) => {
        let Ok (lock) = lock (fd, true) else {fail! ("!lock: " (name))};
        ve.insert ((lock, 0, Vec::new()))},
      Entry::Occupied (oe) => oe.into_mut()};

    let meta = fd.metadata()?;
    let flen = meta.len();
    if (u32::MAX as u64) < flen {fail! ("!u32: " [=flen])}
    let flen = flen as u32;
    let lm = (meta.modified()?.duration_since (UNIX_EPOCH)? .as_millis() / 10) as u64;

    *ofs = if tail < 0 {
      0 .max (flen as i32 + tail) as u32
    } else if 0 < tail {
      if tail < flen as i32 {0} else {tail as u32}
    } else {0};

    let pos = fd.seek (io::SeekFrom::Start (*ofs as u64))?;
    if pos != *ofs as u64 {fail! ("!seek " [=ofs] ' ' [=pos])}
    bytes.clear();
    bytes.reserve_exact ((flen as u64 - *ofs as u64) as usize);
    fd.read_to_end (bytes)?;

    let sig = Signature::calculate (&bytes, SignatureOptions {
      block_size: block as u32,
      crypto_hash_size: hash as u32});
    reqs.push (Req::RsyncProto1 {fx, flen, lm, ofs: *ofs, sig: sig.into_serialized()});

    Re::Ok(())}

  pub fn handle (reps: &[Rep], hostname: &str, state: &mut State) -> Re<()> {
    for rep in reps {match rep {
      Rep::RsyncProto1 {fx, lm, ofs, delta, dlen, bsum:_} => {
        //crate::log! ([=fx] ' ' [=ofs] ' ' [=delta.len()] ' ' [=bsum]);
        let file = &state.files[*fx as usize];
        if !file.hosts.split ('&') .any (|h| h == hostname) {fail! ("!hosts")}
        let Some ((lock, ofs0, mut bytes)) = state.locks.swap_remove (fx) else {fail! ("!lock: " (file.name))};
        let Some (fd) = state.fds.get_mut (fx) else {fail! ("!fd: " (file.name))};
        if *ofs != ofs0 && ofs0 != 0 {bytes.clear()}  // offset is off, start from scratch
        let mut buf = Vec::with_capacity (*dlen as usize);
        fast_rsync::apply_limited (&bytes, &delta, &mut buf, *dlen as usize)?;
        //let bsumʹ = crc16u8 (0xFFFF, &buf);
        //if bsumʹ != *bsum {fail! ("!bsum: " {"{:04X}", bsum} " <> " {"{:04X}", bsumʹ})}
        //⌥ if `tail` was negative, or smaller than the local length of the file,
        //   then we've included a bit of our local tail in the signature,
        //   expecting that bit to match the server side bit for bit..
        //   here we shall check if the prefix of the received `buf` matches the existing `tail`..
        //   if nots, then the server file was modified in place and we ought to REPEAT
        //   the pull without the `tail`
        //⌥ for the sake of performance, and in order not to wear the disk,
        //   shall see how many bytes at the beginning of `bytes` and `buf` are the same
        //   and skip them (by cutting bytes and buf, and incrementing ofs)
        /*
        --- phind -------
        let common_prefix_len = bytes.iter().zip(buf.iter()).take_while(|(a, b)| a == b).count();
        */
        let lm = UNIX_EPOCH + Duration::from_millis (*lm * 10);
        if bytes == buf {  // skip the write if the data is already in place
          fd.set_modified (lm)?;
        } else {
          let pos = fd.seek (io::SeekFrom::Start (*ofs as u64))?;
          if pos != *ofs as u64 {fail! ("!seek " [=ofs] ' ' [=pos])}
          fd.write_all (&buf)?;
          fd.set_len (*ofs as u64 + buf.len() as u64)?;
          fd.set_modified (lm)?;}
        drop (lock);}}}

    Re::Ok(())}}

#[allow(dead_code)] #[repr(packed)] pub struct UStar {
  pub name: [u8; 100],
  pub mode: [u8; 8],
  pub owner: [u8; 8],
  pub group: [u8; 8],
  pub size: [u8; 12],
  pub lm: [u8; 12],  // Leaving empty might produce st_mtime=0 files.
  pub checksum: [u8; 8],
  /// https://github.com/Distrotech/tar/blob/273975b/src/tar.h#L50
  pub typ: u8,
  pub lf: [u8; 100],
  pub ustar: [u8; 6],
  pub uv: [u8; 2],
  pub uowner: [u8; 32],
  pub ugroup: [u8; 32],
  pub dmajor: [u8; 8],
  pub dminor: [u8; 8],
  pub name_prefix: [u8; 155],
  pub pad: [u8; 12]}

impl UStar {
  pub fn o2u64 (mut octal: &[u8]) -> Re<u64> {
    while !octal.is_empty() && !matches! (octal[octal.len() - 1], b'0'..=b'8') {octal = &octal[..octal.len()-1]}
    if octal.is_empty() {return Re::Ok (0)}
    let size = crate::b2s (octal);
    match u64::from_str_radix (size, 8) {
      Ok (l) => Re::Ok (l),
      Err (err) => fail! ("!size " [size] ": " (err))}}

  pub fn size (&self) -> Re<u64> {Self::o2u64 (&self.size)}}
