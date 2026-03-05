//! ### `AArc` Methods
//! * `const fn none() -> Self` Creates empty, uninitialized `AArc`. Ideal for `static` declarations.
//! * `fn empty() -> Self` Creates empty `AArc` with pre-allocated control block.
//! * `fn any<T> (val: T) -> Self` Creates new type-erased `AArc` initialized with given value.
//! * `fn new (val: T) -> Self` Creates new typed `AArc` initialized with given value.
//! * `fn is_none -> bool` Returns `true` if empty or taken.
//! * `fn is_some -> bool` Returns `true` if currently holding a value.
//! * `fn clone -> Self` Clones `AArc`, disconnected if empty.
//! * `fn cloneᵗ -> Result<Self, AArcErr>`
//!   Clones `AArc`, returning error if out of spins or on disconnect.
//! * `fn take -> Result<Option<Box<C>>, AArcErr>` Takes stored value, resetting `AArc` to empty.
//! * `fn spini / spiniʳ<T> (&self, init: &mut dyn FnMut() -> Re<T>) -> Result<AReadGuard<'_, T>, AArcErr>`
//!   Initializes `AArc` if empty, returns read guard. Spins if downcast fails (for `Any`).
//! * `fn spid / spidʳ<T> -> Result<AReadGuard<'_, T>, AArcErr>`
//!   Initializes with `T::default()` if empty. Spins if downcast fails (for `Any`).
//! * `fn spidʷ<T> -> Result<AWriteGuard<'_, T>, AArcErr>`
//!   Initializes with `T::default()` if empty, returning a write guard. Spins if downcast fails (for `Any`).
//! * `fn spin_rd / spinʳ<T> -> Result<AReadGuard<'_, T>, AArcErr>`
//!   Acquires read lock and downcasts to `T`. Spins if downcast fails (for `Any`).
//! * `fn spin_wr / spinʷ<T> -> Result<AWriteGuard<'_, T>, AArcErr>`
//!   Acquires exclusive write lock and downcasts to `T`. Spins if downcast fails (for `Any`).
//! * `fn spin_set / spinˢ<T> (&self, val: T) -> Result<AWriteGuard<'_, T>, AArcErr>`
//!   Acquires write lock and sets new value of type `T`, returning typed guard.
//! * `fn spic_rd / spicʳ<T> (&self, cond: FnMut(&T) -> Re<bool>) -> Result<AReadGuard<'_, T>, AArcErr>`
//!   Conditional read: acquires lock, checks `cond(&T)`; re-spins on `false`. Typed `AArc<T>` only.
//! * `fn spic_wr / spicʷ<T> (&self, cond: FnMut(&T) -> Re<bool>) -> Result<AWriteGuard<'_, T>, AArcErr>`
//!   Conditional write: acquires lock, checks `cond(&T)`; re-spins on `false`. Typed `AArc<T>` only.
//! * `fn status -> (u32, &'static str)` Returns `(read_locks, status_string)`.
//!
//! ### Guard Methods
//! * `AReadGuard::aarc -> AArc<C>` Recovers new `AArc` reference from read guard.
//! * `AReadGuard::map<U> (self, f) -> AReadGuard<'_, U, C>` Maps the inner pointer to a new type.
//! * `AReadGuard::try_map<U, E> (self, f) -> Result<AReadGuard<'_, U, C>, (Self, E)>`
//! * `AReadGuard::wr / wrᵗ (self) -> Result<AWriteGuard<'_, T, C>, (Self, AArcErr)>` Upgrades to write lock.
//! * `AWriteGuard::aarc -> AArc<C>` Recovers new `AArc` reference from write guard.
//! * `AWriteGuard::rd (self) -> AReadGuard<'_, T, C>` Downgrades to read lock.
//! * `AWriteGuard::map<U> (self, f) -> AWriteGuard<'_, U, C>` Maps the inner pointer to a new type.
//! * `AWriteGuard::try_map<U, E> (self, f) -> Result<AWriteGuard<'_, U, C>, (Self, E)>`
//! * `AWriteGuard::set<U> (self, val: U) -> AWriteGuard<'_, U>`
//!   Replaces stored value with new type `U` (or `T`) and returns new typed guard.
//! * `AWriteGuard::take (self) -> Box<C>` Takes stored value while holding write lock.
//!
//! If a thread panics while holding a `AWriteGuard`, the stored data is
//! dropped rather than poisoned. Other threads will see the `AArc` as empty.
//! `AReadGuard`s are safe to drop during a panic; they simply release the read lock.
//! Leaking guards (e.g., via `std::mem::forget`) will permanently
//! lock the `AArc`, preventing future reads or writes.

use crate::{spin_yield, SPIN_OUT};
use crate::re::Re;
use fomat_macros::fomat;
use std::any::Any;
use std::cell::UnsafeCell;
use std::marker::PhantomData;
use std::mem::forget;
use std::ops::{Deref, DerefMut};
use std::ptr;
use std::sync::atomic::{fence, AtomicPtr, AtomicU32, Ordering};
use std::thread::{self, panicking};
use std::time::Duration;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AArcErr {
  SpinOut,
  Disconnect,
  RefcountOverflow,
  ReaderOverflow,
  Init (String)}

impl std::fmt::Display for AArcErr {
  fn fmt (&self, fm: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      AArcErr::SpinOut => write! (fm, "spin-out"),
      AArcErr::Disconnect => write! (fm, "spin-out or disconnect"),
      AArcErr::RefcountOverflow => write! (fm, "refcount overflow"),
      AArcErr::ReaderOverflow => write! (fm, "reader overflow"),
      AArcErr::Init (s) => write! (fm, "init: {}", s)}}}

impl std::error::Error for AArcErr {}

pub struct SpinIt {spins: i32, burst: i32}
impl SpinIt {
  pub fn new (spins: i32) -> Self {Self {
    spins, burst: if spins < 0 {11} else {spins.max (1)}}}}
impl Iterator for SpinIt {
  type Item = bool;
  fn next (&mut self) -> Option<bool> {  // true = spin_yield, false = sleep
    if 0 < self.burst {self.burst -= 1; Some (true)}
    else if self.spins < 0 {self.spins += 3; self.burst = 9; Some (false)}
    else {None}}}

/// Atomic, type-erased, shared mutable container.
///
/// Stores a `dyn Any` behind a spinlock-based RwLock. Lock acquisition performs
/// atomic CAS + `Any::downcast`; the returned guards hold a direct raw pointer
/// to `T`, so subsequent access is zero-cost C-like pointer dereference.
pub struct AArc<T: ?Sized = dyn Any + Send + Sync> {
  ptr: AtomicPtr<ControlBlock<T>>}

struct ControlBlock<T: ?Sized> {
  state: AtomicU32,
  data: UnsafeCell<Option<Box<T>>>}

impl<T: ?Sized> ControlBlock<T> {
  fn replace_data_box (&self, mut b: Box<T>) -> *mut T {
    let ptr = &mut *b as *mut T;
    let old = unsafe {(*self.data.get()).take()};
    unsafe {*self.data.get() = Some (b)}
    drop (old);
    ptr}}

const REF_INC: u32 = 1;
const REF_MASK: u32 = 0x000F_FFFF;
const READ_INC: u32 = 0x0010_0000;
const READ_MASK: u32 = 0x3FF0_0000;
const WRITE_BIT: u32 = 0x4000_0000;
const EMPTY_BIT: u32 = 0x8000_0000;

unsafe impl<C: ?Sized> Send for AArc<C> {}
unsafe impl<C: ?Sized> Sync for AArc<C> {}

impl<C: ?Sized> Clone for AArc<C> {
  /// Clones the AArc.
  ///
  /// Disconnected when instance is completely uninitialized (e.g., from `AArc::none()` before first init).
  /// Taken (`EMPTY_BIT`) instances stay connected.
  fn clone (&self) -> Self {
    let ptr = self.ptr.load (Ordering::Acquire);
    if !ptr.is_null() {
      let cb = unsafe {&*ptr};
      let old = cb.state.fetch_add (REF_INC, Ordering::Relaxed);
      if (old & REF_MASK) == REF_MASK {panic! ()}}
    AArc {ptr: AtomicPtr::new (ptr)}}}

impl<C: ?Sized> Drop for AArc<C> {
  fn drop (&mut self) {
    let ptr = self.ptr.load (Ordering::Acquire);
    if !ptr.is_null() {
      let cb = unsafe {&*ptr};
      let old = cb.state.fetch_sub (REF_INC, Ordering::Release);
      if (old & REF_MASK) == REF_INC {
        fence (Ordering::Acquire);
        debug_assert! ((old & (READ_MASK | WRITE_BIT)) == 0, "Active guards during AArc drop!");
        unsafe {let _ = Box::from_raw (ptr);}}}}}

impl<C: ?Sized> Default for AArc<C> {
  fn default() -> Self {
    Self::none()}}

impl<T: std::fmt::Debug + Send + Sync + 'static> std::fmt::Debug for AArc<T> {
  fn fmt (&self, fm: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let (readers, status) = self.status();
    let mut dbg = fm.debug_struct ("AArc");
    dbg.field ("readers", &readers);
    if !status.is_empty() {dbg.field ("status", &status);}
    if status == "null" || status == "empty" {return dbg.finish()}
    // Opportunistically try to acquire a read lock with exactly 1 attempt (no waiting)
    match self.spinʳ (1) {
      Ok (guard) => dbg.field ("data", &*guard),
      Err (_) => dbg.field ("data", &format_args! ("<locked or empty>"))};
    dbg.finish()}}

impl<C: ?Sized> AArc<C> {
  pub const fn none() -> Self {
    AArc {ptr: AtomicPtr::new (ptr::null_mut())}}
  
  /// Creates an empty `AArc` with a pre-allocated control block.
  /// Useful for creating connected empty arcs as one-shot channels.
  pub fn empty() -> Self {
    let cb = Box::into_raw (Box::new (ControlBlock {
      state: AtomicU32::new (REF_INC | EMPTY_BIT),
      data: UnsafeCell::new (None)}));
    AArc {ptr: AtomicPtr::new (cb)}}

  /// Returns `true` if the `AArc` is uninitialized or its value has been taken.
  pub fn is_none (&self) -> bool {
    let ptr = self.ptr.load (Ordering::Acquire);
    if ptr.is_null() {return true}
    let cb = unsafe {&*ptr};
    (cb.state.load (Ordering::Relaxed) & EMPTY_BIT) != 0}

  /// Returns `true` if the `AArc` currently holds an initialized value.
  pub fn is_some (&self) -> bool {
    !self.is_none()}

  fn try_alloc_cb (&self) -> Option<*mut ControlBlock<C>> {
    let cb = Box::into_raw (Box::new (ControlBlock {
      state: AtomicU32::new (REF_INC | WRITE_BIT | EMPTY_BIT),
      data: UnsafeCell::new (None)}));
    match self.ptr.compare_exchange (ptr::null_mut(), cb, Ordering::Release, Ordering::Acquire) {
      Ok (_) => Some (cb),
      Err (_) => {
        unsafe {let _ = Box::from_raw (cb);}
        None}}}

  /// Clones the AArc, returning an error if out of spins or if would disconnect.
  pub fn cloneᵗ (&self, spins: i32) -> Result<Self, AArcErr> {
    for yieldˀ in SpinIt::new (spins) {
      let ptr = self.ptr.load (Ordering::Acquire);
      if !ptr.is_null() {
        let cb = unsafe {&*ptr};
        let state = cb.state.load (Ordering::Acquire);
        if (state & REF_MASK) == REF_MASK {return Err (AArcErr::RefcountOverflow)}
        if cb.state.compare_exchange_weak (state, state + REF_INC, Ordering::Relaxed, Ordering::Relaxed) .is_ok() {
          return Ok (AArc {ptr: AtomicPtr::new (ptr)})}
        continue}
      if yieldˀ {spin_yield()} else {thread::sleep (Duration::from_millis (30))}}
    Err (AArcErr::Disconnect)}

  pub fn take (&self, spins: i32) -> Result<Option<Box<C>>, AArcErr> {
    for yieldˀ in SpinIt::new (spins) {
      let ptr = self.ptr.load (Ordering::Acquire);
      if ptr.is_null() {return Ok (None)}
      let cb = unsafe {&*ptr};
      let state = cb.state.load (Ordering::Acquire);
      if state & WRITE_BIT == 0 && state & READ_MASK == 0 {
        if cb.state.compare_exchange_weak (state, state | WRITE_BIT, Ordering::Acquire, Ordering::Relaxed) .is_ok() {
          let mut guard = InitGuard {cb: ptr, success: false, _marker: PhantomData};
          let old = unsafe {(*cb.data.get()).take()};
          guard.success = true;
          let mut current = cb.state.load (Ordering::Relaxed);
          loop {
            let new = (current | EMPTY_BIT) & !WRITE_BIT;
            match cb.state.compare_exchange_weak (current, new, Ordering::Release, Ordering::Relaxed) {
              Ok (_) => return Ok (old),
              Err (x) => current = x}}}
        continue}
      if yieldˀ {spin_yield()} else {thread::sleep (Duration::from_millis (30))}}
    Err (AArcErr::SpinOut)}

  /// Returns `(read_locks, status_string)`.
  /// Status is one of: "null", "write-locked", "empty", or "" (initialized, not write-locked).
  pub fn status (&self) -> (u32, &'static str) {
    let ptr = self.ptr.load (Ordering::Acquire);
    if ptr.is_null() {return (0, "null")}
    let cb = unsafe {&*ptr};
    let state = cb.state.load (Ordering::Relaxed);
    let readers = (state & READ_MASK) / READ_INC;
    let status = if (state & WRITE_BIT) != 0 {
      "write-locked"
    } else if (state & EMPTY_BIT) != 0 {
      "empty"
    } else {""};
    (readers, status)}}

impl AArc<dyn Any + Send + Sync> {
  pub fn any<T: Send + Sync + 'static> (val: T) -> Self {
    let cb = Box::into_raw (Box::new (ControlBlock {
      state: AtomicU32::new (REF_INC),
      data: UnsafeCell::new (Some (Box::new (val) as Box<dyn Any + Send + Sync>))}));
    AArc {ptr: AtomicPtr::new (cb)}}
  
  pub fn spiniʳ<T: Send + Sync + 'static> (&self, spins: i32, init: &mut dyn FnMut() -> Re<T>)
  -> Result<AReadGuard<'_, T>, AArcErr> {
    for yieldˀ in SpinIt::new (spins) {
      let ptr = self.ptr.load (Ordering::Acquire);
      if ptr.is_null() {
        if let Some (cb) = self.try_alloc_cb() {
          return self.do_init (cb, init);
        } else {continue}
      } else {
        let cb = unsafe {&*ptr};
        let state = cb.state.load (Ordering::Acquire);
        if state & WRITE_BIT == 0 {
          if state & EMPTY_BIT != 0 {
            if cb.state.compare_exchange (state, state | WRITE_BIT, Ordering::Acquire, Ordering::Relaxed) .is_ok() {
              return self.do_init (ptr, init)}}
          else {
            if (state & READ_MASK) == READ_MASK {return Err (AArcErr::ReaderOverflow)}
            if cb.state.compare_exchange_weak (state, state + READ_INC, Ordering::Acquire, Ordering::Relaxed) .is_ok() {
              let data_ref = unsafe {&*cb.data.get()};
              if let Some (any_box) = data_ref {
                if let Some (typed_ref) = any_box.downcast_ref::<T>() {
                  return Ok (AReadGuard {cb, ptr: typed_ref as *const T, _phantom: PhantomData})}}
              cb.state.fetch_sub (READ_INC, Ordering::Release);}
            else {continue}}}}
      if yieldˀ {spin_yield()} else {thread::sleep (Duration::from_millis (30))}}
    Err (AArcErr::SpinOut)}

  fn do_init<T: Send + Sync + 'static> (&self,
  cb_ptr: *mut ControlBlock<dyn Any + Send + Sync>, init: &mut dyn FnMut() -> Re<T>)
  -> Result<AReadGuard<'_, T>, AArcErr> {
    let mut guard = InitGuard {cb: cb_ptr, success: false, _marker: PhantomData};
    match init() {
      Re::Ok (val) => {
        let cb = unsafe {&*cb_ptr};
        let ptr = cb.replace_data_box (Box::new (val) as Box<dyn Any + Send + Sync>) as *const _ as *const T;
        guard.success = true;

        let mut current = cb.state.load (Ordering::Relaxed);
        loop {
          let new = (current & !WRITE_BIT & !EMPTY_BIT) + READ_INC;
          match cb.state.compare_exchange_weak (current, new, Ordering::Release, Ordering::Relaxed) {
            Ok (_) => break, Err (x) => current = x}}
        Ok (AReadGuard {cb, ptr, _phantom: PhantomData})}
      Re::Err (e) => Err (AArcErr::Init (e))}}

  pub fn spidʳ<T: Default + Send + Sync + 'static> (&self, spins: i32) -> Result<AReadGuard<'_, T>, AArcErr> {
    self.spiniʳ (spins, &mut || Re::Ok (T::default()))}

  pub fn spini<T: Send + Sync + 'static> (&self, init: &mut dyn FnMut() -> Re<T>)
  -> Result<AReadGuard<'_, T>, AArcErr> {
    self.spiniʳ (unsafe {SPIN_OUT as i32}, init)}

  pub fn spid<T: Default + Send + Sync + 'static> (&self) -> Result<AReadGuard<'_, T>, AArcErr> {
    self.spidʳ (unsafe {SPIN_OUT as i32})}

  pub fn spidʷ<T: Default + Send + Sync + 'static> (&self, spins: i32) -> Result<AWriteGuard<'_, T>, AArcErr> {
    for yieldˀ in SpinIt::new (spins) {
      let ptr = self.ptr.load (Ordering::Acquire);
      if ptr.is_null() {
        if let Some (cb_ptr) = self.try_alloc_cb() {
          let mut guard = InitGuard {cb: cb_ptr, success: false, _marker: PhantomData};
          let cb = unsafe {&*cb_ptr};
          let data_ptr = cb.replace_data_box
            (Box::new (T::default()) as Box<dyn Any + Send + Sync>) as *mut _ as *mut T;
          cb.state.fetch_and (!EMPTY_BIT, Ordering::Release);
          guard.success = true;
          return Ok (AWriteGuard {cb, ptr: data_ptr, _phantom: PhantomData})
        } else {continue}
      } else {
        let cb = unsafe {&*ptr};
        let state = cb.state.load (Ordering::Acquire);
        if state & WRITE_BIT == 0 && state & READ_MASK == 0 {
          if state & EMPTY_BIT != 0 {
            if cb.state.compare_exchange_weak
            (state, state | WRITE_BIT, Ordering::Acquire, Ordering::Relaxed) .is_ok() {
              let mut guard = InitGuard {cb: ptr, success: false, _marker: PhantomData};
              let data_ptr = cb.replace_data_box
                (Box::new (T::default()) as Box<dyn Any + Send + Sync>) as *mut _ as *mut T;
              cb.state.fetch_and (!EMPTY_BIT, Ordering::Release);
              guard.success = true;
              return Ok (AWriteGuard {cb: ptr, ptr: data_ptr, _phantom: PhantomData})}
          } else {
            if cb.state.compare_exchange_weak
            (state, state | WRITE_BIT, Ordering::Acquire, Ordering::Relaxed) .is_ok() {
              let data_mut = unsafe {&mut *cb.data.get()};
              if let Some (any_box) = data_mut {
                if let Some (typed_mut) = any_box.downcast_mut::<T>() {
                  return Ok (AWriteGuard {cb: ptr, ptr: typed_mut as *mut T, _phantom: PhantomData})}}
              cb.state.fetch_and (!WRITE_BIT, Ordering::Release);}
            else {continue}}}}
      if yieldˀ {spin_yield()} else {thread::sleep (Duration::from_millis (30))}}
    Err (AArcErr::SpinOut)}

  pub fn spinʳ<T: 'static> (&self, spins: i32) -> Result<AReadGuard<'_, T>, AArcErr> {
    // All expensive work (atomic CAS, downcast) happens here.
    // The returned AReadGuard holds *const T — zero-cost deref after this point.
    for yieldˀ in SpinIt::new (spins) {
      let ptr = self.ptr.load (Ordering::Acquire);
      if !ptr.is_null() {
        let cb = unsafe {&*ptr};
        let state = cb.state.load (Ordering::Acquire);
        if state & WRITE_BIT == 0 && state & EMPTY_BIT == 0 {
          if (state & READ_MASK) == READ_MASK {return Err (AArcErr::ReaderOverflow)}
          if cb.state.compare_exchange_weak (state, state + READ_INC, Ordering::Acquire, Ordering::Relaxed) .is_ok() {
            let data_ref = unsafe {&*cb.data.get()};
            if let Some (any_box) = data_ref {
              if let Some (typed_ref) = any_box.downcast_ref::<T>() {
                return Ok (AReadGuard {cb, ptr: typed_ref as *const T, _phantom: PhantomData})}}
            cb.state.fetch_sub (READ_INC, Ordering::Release);}
          else {continue}}}
      if yieldˀ {spin_yield()} else {thread::sleep (Duration::from_millis (30))}}
    Err (AArcErr::SpinOut)}

  pub fn spin_rd<T: 'static> (&self) -> Result<AReadGuard<'_, T>, AArcErr> {
    self.spinʳ (unsafe {SPIN_OUT as i32})}

  pub fn spinʷ<T: 'static> (&self, spins: i32) -> Result<AWriteGuard<'_, T>, AArcErr> {
    // All expensive work (atomic CAS, downcast) happens here.
    // The returned AWriteGuard holds *mut T — zero-cost deref after this point.
    for yieldˀ in SpinIt::new (spins) {
      let ptr = self.ptr.load (Ordering::Acquire);
      if !ptr.is_null() {
        let cb = unsafe {&*ptr};
        let state = cb.state.load (Ordering::Acquire);
        if state & WRITE_BIT == 0 && state & READ_MASK == 0 && state & EMPTY_BIT == 0 {
          if cb.state.compare_exchange_weak (state, state | WRITE_BIT, Ordering::Acquire, Ordering::Relaxed).is_ok() {
            let data_mut = unsafe {&mut *cb.data.get()};
            if let Some (any_box) = data_mut {
              if let Some (typed_mut) = any_box.downcast_mut::<T>() {
                return Ok (AWriteGuard {cb, ptr: typed_mut as *mut T, _phantom: PhantomData})}}
            cb.state.fetch_and (!WRITE_BIT, Ordering::Release);}
          else {continue}}}
      if yieldˀ {spin_yield()} else {thread::sleep (Duration::from_millis (30))}}
    Err (AArcErr::SpinOut)}

  pub fn spin_wr<T: 'static> (&self) -> Result<AWriteGuard<'_, T>, AArcErr> {
    self.spinʷ (unsafe {SPIN_OUT as i32})}

  pub fn spinˢ<T: Send + Sync + 'static> (&self, spins: i32, val: T) -> Result<AWriteGuard<'_, T>, AArcErr> {
    for yieldˀ in SpinIt::new (spins) {
      let ptr = self.ptr.load (Ordering::Acquire);
      if ptr.is_null() {
        if let Some (cb_ptr) = self.try_alloc_cb() {
          // InitGuard ensures cleanup if any operation panics before we return the AWriteGuard
          let mut guard = InitGuard {cb: cb_ptr, success: false, _marker: PhantomData};
          let cb = unsafe {&*cb_ptr};
          let data_ptr = cb.replace_data_box (Box::new (val) as Box<dyn Any + Send + Sync>) as *mut _ as *mut T;
          cb.state.fetch_and (!EMPTY_BIT, Ordering::Release);
          guard.success = true;
          return Ok (AWriteGuard {cb, ptr: data_ptr, _phantom: PhantomData})
        } else {continue}
      } else {
        let cb = unsafe {&*ptr};
        let state = cb.state.load (Ordering::Acquire);
        if state & WRITE_BIT == 0 && state & READ_MASK == 0 {
          if cb.state.compare_exchange_weak (state, state | WRITE_BIT, Ordering::Acquire, Ordering::Relaxed) .is_ok() {
            // Use InitGuard to ensure WRITE_BIT is cleared if `drop(old)` panics.
            // Without this, a panic during drop would leave the lock permanently stuck.
            let mut guard = InitGuard {cb: ptr, success: false, _marker: PhantomData};
            let data_ptr = cb.replace_data_box (Box::new (val) as Box<dyn Any + Send + Sync>) as *mut _ as *mut T;
            cb.state.fetch_and (!EMPTY_BIT, Ordering::Release);
            guard.success = true;
            return Ok (AWriteGuard {cb, ptr: data_ptr, _phantom: PhantomData})}
          continue}}
      if yieldˀ {spin_yield()} else {thread::sleep (Duration::from_millis (30))}}
    Err (AArcErr::SpinOut)}

  pub fn spin_set<T: Send + Sync + 'static> (&self, val: T) -> Result<AWriteGuard<'_, T>, AArcErr> {
    self.spinˢ (unsafe {SPIN_OUT as i32}, val)}}

impl<T: Send + Sync + 'static> AArc<T> {
  pub fn new (val: T) -> Self {
    let cb = Box::into_raw (Box::new (ControlBlock {
      state: AtomicU32::new (REF_INC),
      data: UnsafeCell::new (Some (Box::new (val)))}));
    AArc {ptr: AtomicPtr::new (cb)}}

  pub fn spiniʳ (&self, spins: i32, init: &mut dyn FnMut() -> Re<T>)
  -> Result<AReadGuard<'_, T, T>, AArcErr> {
    for yieldˀ in SpinIt::new (spins) {
      let ptr = self.ptr.load (Ordering::Acquire);
      if ptr.is_null() {
        if let Some (cb) = self.try_alloc_cb() {
          return self.do_init (cb, init);
        } else {continue}
      } else {
        let cb = unsafe {&*ptr};
        let state = cb.state.load (Ordering::Acquire);
        if state & WRITE_BIT == 0 {
          if state & EMPTY_BIT != 0 {
            if cb.state.compare_exchange (state, state | WRITE_BIT, Ordering::Acquire, Ordering::Relaxed) .is_ok() {
              return self.do_init (ptr, init)}}
          else {
            if (state & READ_MASK) == READ_MASK {return Err (AArcErr::ReaderOverflow)}
            if cb.state.compare_exchange_weak (state, state + READ_INC, Ordering::Acquire, Ordering::Relaxed) .is_ok() {
              let data_ref = unsafe {&*cb.data.get()};
              if let Some (typed_box) = data_ref {
                return Ok (AReadGuard {cb, ptr: &**typed_box as *const T, _phantom: PhantomData})}
              cb.state.fetch_sub (READ_INC, Ordering::Release);}
            else {continue}}}}
      if yieldˀ {spin_yield()} else {thread::sleep (Duration::from_millis (30))}}
    Err (AArcErr::SpinOut)}

  fn do_init (&self, cb_ptr: *mut ControlBlock<T>, init: &mut dyn FnMut() -> Re<T>)
  -> Result<AReadGuard<'_, T, T>, AArcErr> {
    let mut guard = InitGuard {cb: cb_ptr, success: false, _marker: PhantomData};
    match init() {
      Re::Ok (val) => {
        let cb = unsafe {&*cb_ptr};
        let ptr = cb.replace_data_box (Box::new (val));
        guard.success = true;

        let mut current = cb.state.load (Ordering::Relaxed);
        loop {
          let new = (current & !WRITE_BIT & !EMPTY_BIT) + READ_INC;
          match cb.state.compare_exchange_weak (current, new, Ordering::Release, Ordering::Relaxed) {
            Ok (_) => break, Err (x) => current = x}}
        Ok (AReadGuard {cb, ptr, _phantom: PhantomData})}
      Re::Err (e) => Err (AArcErr::Init (e))}}

  pub fn spidʳ (&self, spins: i32) -> Result<AReadGuard<'_, T, T>, AArcErr> where T: Default {
    self.spiniʳ (spins, &mut || Re::Ok (T::default()))}

  pub fn spini (&self, init: &mut dyn FnMut() -> Re<T>) -> Result<AReadGuard<'_, T, T>, AArcErr> {
    self.spiniʳ (unsafe {SPIN_OUT as i32}, init)}

  pub fn spid (&self) -> Result<AReadGuard<'_, T, T>, AArcErr> where T: Default {
    self.spidʳ (unsafe {SPIN_OUT as i32})}

  pub fn spidʷ (&self, spins: i32) -> Result<AWriteGuard<'_, T, T>, AArcErr> where T: Default {
    for yieldˀ in SpinIt::new (spins) {
      let ptr = self.ptr.load (Ordering::Acquire);
      if ptr.is_null() {
        if let Some (cb_ptr) = self.try_alloc_cb() {
          let mut guard = InitGuard {cb: cb_ptr, success: false, _marker: PhantomData};
          let cb = unsafe {&*cb_ptr};
          let data_ptr = cb.replace_data_box (Box::new (T::default()));
          cb.state.fetch_and (!EMPTY_BIT, Ordering::Release);
          guard.success = true;
          return Ok (AWriteGuard {cb, ptr: data_ptr, _phantom: PhantomData})
        } else {continue}
      } else {
        let cb = unsafe {&*ptr};
        let state = cb.state.load (Ordering::Acquire);
        if state & WRITE_BIT == 0 && state & READ_MASK == 0 {
          if state & EMPTY_BIT != 0 {
            if cb.state.compare_exchange_weak
            (state, state | WRITE_BIT, Ordering::Acquire, Ordering::Relaxed) .is_ok() {
              let mut guard = InitGuard {cb: ptr, success: false, _marker: PhantomData};
              let data_ptr = cb.replace_data_box (Box::new (T::default()));
              cb.state.fetch_and (!EMPTY_BIT, Ordering::Release);
              guard.success = true;
              return Ok (AWriteGuard {cb: ptr, ptr: data_ptr, _phantom: PhantomData})}
          } else {
            if cb.state.compare_exchange_weak
            (state, state | WRITE_BIT, Ordering::Acquire, Ordering::Relaxed) .is_ok() {
              let data_mut = unsafe {&mut *cb.data.get()};
              if let Some (typed_box) = data_mut {
                return Ok (AWriteGuard {cb: ptr, ptr: &mut **typed_box as *mut T, _phantom: PhantomData})}
              cb.state.fetch_and (!WRITE_BIT, Ordering::Release);}
            else {continue}}}}
      if yieldˀ {spin_yield()} else {thread::sleep (Duration::from_millis (30))}}
    Err (AArcErr::SpinOut)}

  pub fn spinʳ (&self, spins: i32) -> Result<AReadGuard<'_, T, T>, AArcErr> {
    for yieldˀ in SpinIt::new (spins) {
      let ptr = self.ptr.load (Ordering::Acquire);
      if !ptr.is_null() {
        let cb = unsafe {&*ptr};
        let state = cb.state.load (Ordering::Acquire);
        if state & WRITE_BIT == 0 && state & EMPTY_BIT == 0 {
          if (state & READ_MASK) == READ_MASK {return Err (AArcErr::ReaderOverflow)}
          if cb.state.compare_exchange_weak (state, state + READ_INC, Ordering::Acquire, Ordering::Relaxed) .is_ok() {
            let data_ref = unsafe {&*cb.data.get()};
            if let Some (typed_box) = data_ref {
              return Ok (AReadGuard {cb, ptr: &**typed_box as *const T, _phantom: PhantomData})}
            cb.state.fetch_sub (READ_INC, Ordering::Release);}
          else {continue}}}
      if yieldˀ {spin_yield()} else {thread::sleep (Duration::from_millis (30))}}
    Err (AArcErr::SpinOut)}

  pub fn spin_rd (&self) -> Result<AReadGuard<'_, T, T>, AArcErr> {
    self.spinʳ (unsafe {SPIN_OUT as i32})}

  pub fn spicʳ (&self, spins: i32, cond: &mut dyn FnMut(&T) -> Re<bool>) -> Result<AReadGuard<'_, T, T>, AArcErr> {
    let mut spinc = SpinIt::new (spins);
    while let Some (yieldˀ) = spinc.next() {
      let ptr = self.ptr.load (Ordering::Acquire);
      if !ptr.is_null() {
        let cb = unsafe {&*ptr};
        let state = cb.state.load (Ordering::Acquire);
        if state & WRITE_BIT == 0 && state & EMPTY_BIT == 0 {
          if (state & READ_MASK) == READ_MASK {return Err (AArcErr::ReaderOverflow)}
          if cb.state.compare_exchange_weak (state, state + READ_INC, Ordering::Acquire, Ordering::Relaxed) .is_ok() {
            let data_ref = unsafe {&*cb.data.get()};
            if let Some (typed_box) = data_ref {
              match cond (&**typed_box) {
                Re::Ok (true) => return Ok (AReadGuard {cb, ptr: &**typed_box as *const T, _phantom: PhantomData}),
                Re::Ok (false) => {
                  cb.state.fetch_sub (READ_INC, Ordering::Release);
                  if spins < 0 {spinc.burst = 0;}},
                Re::Err (e) => {
                  cb.state.fetch_sub (READ_INC, Ordering::Release);
                  return Err (AArcErr::Init (e));}}}
            else {
              cb.state.fetch_sub (READ_INC, Ordering::Release);}
          } else {continue}}}
      if yieldˀ {spin_yield()} else {thread::sleep (Duration::from_millis (30))}}
    Err (AArcErr::SpinOut)}

  pub fn spic_rd (&self, cond: &mut dyn FnMut(&T) -> Re<bool>) -> Result<AReadGuard<'_, T, T>, AArcErr> {
    self.spicʳ (unsafe {SPIN_OUT as i32}, cond)}

  pub fn spinʷ (&self, spins: i32) -> Result<AWriteGuard<'_, T, T>, AArcErr> {
    for yieldˀ in SpinIt::new (spins) {
      let ptr = self.ptr.load (Ordering::Acquire);
      if !ptr.is_null() {
        let cb = unsafe {&*ptr};
        let state = cb.state.load (Ordering::Acquire);
        if state & WRITE_BIT == 0 && state & READ_MASK == 0 && state & EMPTY_BIT == 0 {
          if cb.state.compare_exchange_weak (state, state | WRITE_BIT, Ordering::Acquire, Ordering::Relaxed).is_ok() {
            let data_mut = unsafe {&mut *cb.data.get()};
            if let Some (typed_box) = data_mut {
              return Ok (AWriteGuard {cb, ptr: &mut **typed_box as *mut T, _phantom: PhantomData})}
            cb.state.fetch_and (!WRITE_BIT, Ordering::Release);}
          else {continue}}}
      if yieldˀ {spin_yield()} else {thread::sleep (Duration::from_millis (30))}}
    Err (AArcErr::SpinOut)}

  pub fn spin_wr (&self) -> Result<AWriteGuard<'_, T, T>, AArcErr> {
    self.spinʷ (unsafe {SPIN_OUT as i32})}

  pub fn spicʷ (&self, spins: i32, cond: &mut dyn FnMut(&T) -> Re<bool>) -> Result<AWriteGuard<'_, T, T>, AArcErr> {
    let mut spinc = SpinIt::new (spins);
    while let Some (yieldˀ) = spinc.next() {
      let ptr = self.ptr.load (Ordering::Acquire);
      if !ptr.is_null() {
        let cb = unsafe {&*ptr};
        let state = cb.state.load (Ordering::Acquire);
        if state & WRITE_BIT == 0 && state & READ_MASK == 0 && state & EMPTY_BIT == 0 {
          if cb.state.compare_exchange_weak (state, state | WRITE_BIT, Ordering::Acquire, Ordering::Relaxed).is_ok() {
            let data_mut = unsafe {&mut *cb.data.get()};
            if let Some (typed_box) = data_mut {
              match cond (&**typed_box) {
                Re::Ok (true) => return Ok (AWriteGuard {cb, ptr: &mut **typed_box as *mut T, _phantom: PhantomData}),
                Re::Ok (false) => {
                  cb.state.fetch_and (!WRITE_BIT, Ordering::Release);
                  if spins < 0 {spinc.burst = 0;}},
                Re::Err (e) => {
                  cb.state.fetch_and (!WRITE_BIT, Ordering::Release);
                  return Err (AArcErr::Init (e));}}}
            else {
              cb.state.fetch_and (!WRITE_BIT, Ordering::Release);}
          } else {continue}}}
      if yieldˀ {spin_yield()} else {thread::sleep (Duration::from_millis (30))}}
    Err (AArcErr::SpinOut)}

  pub fn spic_wr (&self, cond: &mut dyn FnMut(&T) -> Re<bool>) -> Result<AWriteGuard<'_, T, T>, AArcErr> {
    self.spicʷ (unsafe {SPIN_OUT as i32}, cond)}

  pub fn spinˢ (&self, spins: i32, val: T) -> Result<AWriteGuard<'_, T, T>, AArcErr> {
    for yieldˀ in SpinIt::new (spins) {
      let ptr = self.ptr.load (Ordering::Acquire);
      if ptr.is_null() {
        if let Some (cb_ptr) = self.try_alloc_cb() {
          let mut guard = InitGuard {cb: cb_ptr, success: false, _marker: PhantomData};
          let cb = unsafe {&*cb_ptr};
          let data_ptr = cb.replace_data_box (Box::new (val));
          cb.state.fetch_and (!EMPTY_BIT, Ordering::Release);
          guard.success = true;
          return Ok (AWriteGuard {cb, ptr: data_ptr, _phantom: PhantomData})
        } else {continue}
      } else {
        let cb = unsafe {&*ptr};
        let state = cb.state.load (Ordering::Acquire);
        if state & WRITE_BIT == 0 && state & READ_MASK == 0 {
          if cb.state.compare_exchange_weak (state, state | WRITE_BIT, Ordering::Acquire, Ordering::Relaxed) .is_ok() {
            let mut guard = InitGuard {cb: ptr, success: false, _marker: PhantomData};
            let data_ptr = cb.replace_data_box (Box::new (val));
            cb.state.fetch_and (!EMPTY_BIT, Ordering::Release);
            guard.success = true;
            return Ok (AWriteGuard {cb, ptr: data_ptr, _phantom: PhantomData})}
          continue}}
      if yieldˀ {spin_yield()} else {thread::sleep (Duration::from_millis (30))}}
    Err (AArcErr::SpinOut)}

  pub fn spin_set (&self, val: T) -> Result<AWriteGuard<'_, T, T>, AArcErr> {
    self.spinˢ (unsafe {SPIN_OUT as i32}, val)}
}

struct InitGuard<'a, C: ?Sized> {
  cb: *mut ControlBlock<C>,
  success: bool,
  _marker: PhantomData<&'a ()>}

impl<'a, C: ?Sized> Drop for InitGuard<'a, C> {
  fn drop (&mut self) {
    if !self.success {
      let cb = unsafe {&*self.cb};
      let old = unsafe {(*cb.data.get()).take()};
      drop (old);
      let mut current = cb.state.load (Ordering::Relaxed);
      loop {
        let new = (current | EMPTY_BIT) & !WRITE_BIT;
        match cb.state.compare_exchange_weak (current, new, Ordering::Release, Ordering::Relaxed) {
          Ok (_) => break, Err (x) => current = x}}}}}

/// Read guard holding a direct `*const T` obtained during lock acquisition.
pub struct AReadGuard<'a, T: ?Sized, C: ?Sized = dyn Any + Send + Sync> {
  cb: *const ControlBlock<C>,
  ptr: *const T,
  _phantom: PhantomData<&'a T>}

impl<'a, T: ?Sized + std::fmt::Debug, C: ?Sized> std::fmt::Debug for AReadGuard<'a, T, C> {
  fn fmt (&self, fm: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    std::fmt::Debug::fmt (&**self, fm)}}

impl<'a, T: ?Sized, C: ?Sized> Deref for AReadGuard<'a, T, C> {
  type Target = T;
  fn deref (&self) -> &T {
    // Zero-cost: raw pointer deref, no atomics or downcast.
    unsafe {&*self.ptr}}}

impl<'a, T: ?Sized, C: ?Sized> AReadGuard<'a, T, C> {
  pub fn aarc (&self) -> AArc<C> {
    let cb = unsafe {&*self.cb};
    let old = cb.state.fetch_add (REF_INC, Ordering::Relaxed);
    if (old & REF_MASK) == REF_MASK {panic! ()}
    AArc {ptr: AtomicPtr::new (self.cb as *mut _)}}

  pub fn map<U: ?Sized, F: FnOnce (&T) -> &U> (self, f: F) -> AReadGuard<'a, U, C> {
    let ptr = f (unsafe {&*self.ptr}) as *const U;
    let cb = self.cb;
    forget (self);
    AReadGuard {cb, ptr, _phantom: PhantomData}}

  pub fn try_map<U: ?Sized, E, F: FnOnce (&T) -> Result<&U, E>> (self, f: F)
  -> Result<AReadGuard<'a, U, C>, (Self, E)> {
    match f (unsafe {&*self.ptr}) {
      Ok (r) => {
        let ptr = r as *const U;
        let cb = self.cb;
        forget (self);
        Ok (AReadGuard {cb, ptr, _phantom: PhantomData})}
      Err (e) => Err ((self, e))}}

  /// Attempts to upgrade the read lock to a write lock without downcasting.
  /// 
  /// **Warning:** If two threads hold read locks and both attempt to upgrade, 
  /// they will spin-out, as neither would release their read lock.
  /// On failure the read guard is returned in the error tuple.
  pub fn wrᵗ (self, spins: i32) -> Result<AWriteGuard<'a, T, C>, (Self, AArcErr)> {
    let cb = unsafe {&*self.cb};
    for yieldˀ in SpinIt::new (spins) {
      let state = cb.state.load (Ordering::Acquire);
      if (state & READ_MASK) == READ_INC {
        if cb.state.compare_exchange_weak (state, (state - READ_INC) | WRITE_BIT, Ordering::Acquire, Ordering::Relaxed) .is_ok() {
          let ptr = self.ptr as *mut T;
          let cb_ptr = self.cb;
          forget (self);
          return Ok (AWriteGuard {cb: cb_ptr, ptr, _phantom: PhantomData})}}
      if yieldˀ {spin_yield()} else {thread::sleep (Duration::from_millis (30))}}
    Err ((self, AArcErr::SpinOut))}

  pub fn wr (self) -> Result<AWriteGuard<'a, T, C>, (Self, AArcErr)> {
    self.wrᵗ (unsafe {SPIN_OUT as i32})}}

impl<'a, T: ?Sized, C: ?Sized> Drop for AReadGuard<'a, T, C> {
  fn drop (&mut self) {
    let cb = unsafe {&*self.cb};
    cb.state.fetch_sub (READ_INC, Ordering::Release);}}

/// Write guard holding a direct `*mut T` obtained during lock acquisition.
pub struct AWriteGuard<'a, T: ?Sized, C: ?Sized = dyn Any + Send + Sync> {
  cb: *const ControlBlock<C>,
  ptr: *mut T,
  _phantom: PhantomData<&'a mut T>}

impl<'a, T: ?Sized + std::fmt::Debug, C: ?Sized> std::fmt::Debug for AWriteGuard<'a, T, C> {
  fn fmt (&self, fm: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    std::fmt::Debug::fmt (&**self, fm)}}

impl<'a, T: ?Sized, C: ?Sized> Deref for AWriteGuard<'a, T, C> {
  type Target = T;
  fn deref (&self) -> &T {
    // Zero-cost: raw pointer deref, no atomics or downcast.
    unsafe {&*self.ptr}}}

impl<'a, T: ?Sized, C: ?Sized> DerefMut for AWriteGuard<'a, T, C> {
  fn deref_mut (&mut self) -> &mut T {
    // Zero-cost: raw pointer deref, no atomics or downcast.
    unsafe {&mut *self.ptr}}}

impl<'a, T: ?Sized, C: ?Sized> AWriteGuard<'a, T, C> {
  pub fn aarc (&self) -> AArc<C> {
    let cb = unsafe {&*self.cb};
    let old = cb.state.fetch_add (REF_INC, Ordering::Relaxed);
    if (old & REF_MASK) == REF_MASK {panic! ()}
    AArc {ptr: AtomicPtr::new (self.cb as *mut _)}}

  pub fn rd (self) -> AReadGuard<'a, T, C> {
    let cb = unsafe {&*self.cb};
    cb.state.fetch_sub (WRITE_BIT - READ_INC, Ordering::Release);
    let ptr = self.ptr as *const T;
    let cb_ptr = self.cb;
    forget (self);
    AReadGuard {cb: cb_ptr, ptr, _phantom: PhantomData}}

  pub fn map<U: ?Sized, F: FnOnce (&mut T) -> &mut U> (self, f: F) -> AWriteGuard<'a, U, C> {
    let ptr = f (unsafe {&mut *self.ptr}) as *mut U;
    let cb = self.cb;
    forget (self);
    AWriteGuard {cb, ptr, _phantom: PhantomData}}

  pub fn try_map<U: ?Sized, E, F: FnOnce (&mut T) -> Result<&mut U, E>> (self, f: F)
  -> Result<AWriteGuard<'a, U, C>, (Self, E)> {
    match f (unsafe {&mut *self.ptr}) {
      Ok (r) => {
        let ptr = r as *mut U;
        let cb = self.cb;
        forget (self);
        Ok (AWriteGuard {cb, ptr, _phantom: PhantomData})}
      Err (e) => Err ((self, e))}}

  pub fn take (self) -> Box<C> {
    let cb = unsafe {&*self.cb};
    let old = unsafe {(*cb.data.get()).take()};
    let mut current = cb.state.load (Ordering::Relaxed);
    loop {
      let new = (current | EMPTY_BIT) & !WRITE_BIT;
      match cb.state.compare_exchange_weak (current, new, Ordering::Release, Ordering::Relaxed) {
        Ok (_) => break, Err (x) => current = x}}
    forget (self);
    old.unwrap()}}

impl<'a, T: ?Sized> AWriteGuard<'a, T> {
  pub fn set<U: Send + Sync + 'static> (self, val: U) -> AWriteGuard<'a, U> {
    let cb = unsafe {&*self.cb};
    // Drop-safe: if drop(old) panics inside replace_data_box, `forget(self)` below has not yet run,
    // so `AWriteGuard::drop` executes during unwind. That impl checks
    // `panicking()`, takes (now-new) data, drops it, clears WRITE_BIT and
    // sets EMPTY_BIT. No InitGuard needed — AWriteGuard itself is the guard.
    let ptr = cb.replace_data_box (Box::new (val) as Box<dyn Any + Send + Sync>) as *mut _ as *mut U;
    cb.state.fetch_and (!EMPTY_BIT, Ordering::Release);
    let guard = AWriteGuard {cb: self.cb, ptr, _phantom: PhantomData};
    forget (self);
    guard}}

impl<'a, T: Send + Sync + 'static> AWriteGuard<'a, T, T> {
  pub fn set (self, val: T) -> AWriteGuard<'a, T, T> {
    let cb = unsafe {&*self.cb};
    let ptr = cb.replace_data_box (Box::new (val));
    cb.state.fetch_and (!EMPTY_BIT, Ordering::Release);
    let guard = AWriteGuard {cb: self.cb, ptr, _phantom: PhantomData};
    forget (self);
    guard}}

impl<'a, T: ?Sized, C: ?Sized> Drop for AWriteGuard<'a, T, C> {
  fn drop (&mut self) {
    let cb = unsafe {&*self.cb};
    if panicking() {
      let old = unsafe {(*cb.data.get()).take()};
      drop (old);
      let mut current = cb.state.load (Ordering::Relaxed);
      loop {
        let new = (current | EMPTY_BIT) & !WRITE_BIT;
        match cb.state.compare_exchange_weak (current, new, Ordering::Release, Ordering::Relaxed) {
          Ok (_) => break, Err (x) => current = x}}
    } else {
      cb.state.fetch_and (!WRITE_BIT, Ordering::Release);}}}

#[cfg(test)]
mod tests {
  extern crate test;
  use crate::fail;
  use std::panic::{self, UnwindSafe};
  use std::sync::{Arc, Mutex, RwLock};
  use std::sync::atomic::AtomicUsize;
  use std::thread;
  use super::*;
  type BoxFnI32 = Box<dyn Fn() -> i32 + Send + Sync>;
  type BoxFnMutI32 = Box<dyn FnMut() -> i32 + Send + Sync>;
  type BoxFnReI32 = Box<dyn Fn() -> Result<i32, AArcErr> + Send + Sync>;
  type BoxFnMutReU32 = Box<dyn FnMut() -> Result<u32, AArcErr> + Send + Sync>;

  #[test] fn spid_w() {
    let aarc: AArc = AArc::none();
    assert! (aarc.is_none());
    assert_eq! (aarc.status(), (0, "null"));  // Empty/uninitialized has no locks.
    // spidʷ initializes with T::default() if empty, returns AWriteGuard
    let mut guard = aarc.spidʷ::<i32> (100) .unwrap();
    assert! (aarc.is_some());
    assert_eq! (aarc.status(), (0, "write-locked"));  // AWriteGuard holds the exclusive write lock.
    assert_eq! (*guard, 0);
    *guard = 42;
    
    let read_guard = guard.rd();
    assert_eq! (aarc.status(), (1, ""));  // AReadGuard holds a shared read lock.
    assert_eq! (*read_guard, 42)}

  #[test] fn spid_w_existing() {
    let aarc: AArc = AArc::none();
    let _ = aarc.spin_set (5i32) .unwrap();
    
    // spidʷ should NOT overwrite with default (0) if already initialized
    let guard = aarc.spidʷ::<i32> (100) .unwrap();
    assert_eq! (*guard, 5)}

  #[test] fn basic_init_and_read() {
    let aarc: AArc = AArc::none();  // start empty
    // spid initializes with T::default() if empty, returns AReadGuard
    let guard = aarc.spid::<i32>().unwrap();
    assert_eq! (aarc.status(), (1, ""));  // Snapshot shows 1 reader, 0 writers.
    assert_eq! (*guard, 0);  // AReadGuard derefs to &T.

    let recovered_aarc = guard.aarc();
    assert_eq! (recovered_aarc.status(), (1, ""));

    drop (guard);  // Must drop AReadGuard before spin_wr; no reader→writer upgrade.

    // spin_wr acquires exclusive write lock
    let write_guard = aarc.spin_wr::<i32>().unwrap();
    assert_eq! (aarc.status(), (0, "write-locked"));  // Snapshot shows 0 readers, 1 writer.

    let recovered_aarc2 = write_guard.aarc();
    assert_eq! (recovered_aarc2.status(), (0, "write-locked"));

    // set drops the old value inside, then stores the new one (can even change type)
    let mut write_guard = write_guard.set (42i32);
    assert_eq! (*write_guard, 42);
    *write_guard = 43;  // DerefMut allows in-place mutation
    
    let read_guard = write_guard.rd();
    assert_eq! (*read_guard, 43);}  // AReadGuard dropped: clears READ_INC, data persists.

  #[test] fn re_init() {
    use crate::fail;

    let aarc: AArc = AArc::none();
    let err = aarc.spini::<i32> (&mut || {fail! ("init failed")}) .unwrap_err();
    match err {
      AArcErr::Init (msg) => assert! (msg.ends_with ("] init failed")),
      _ => panic! ("Expected AArcErr::Init")}

    let guard = aarc.spini::<i32> (&mut || Re::Ok (42)) .unwrap();
    assert_eq! (*guard, 42);}

  #[test] fn closure_storage() {
    let aarc: AArc = AArc::none();

    // spiniʳ with custom spin limit; closure-based init
    let _ = aarc.spiniʳ::<BoxFnI32> (100, &mut || {
      Re::Ok (Box::new (|| 77))}) .unwrap();

    // Fn closures callable through AReadGuard (Deref gives &self)
    let read_guard = aarc.spin_rd::<BoxFnI32>().unwrap();
    assert_eq! (read_guard(), 77);
    drop (read_guard);

    // spinˢ acquires write, drops old Box<dyn Fn> closure, stores new Box<dyn FnMut>.
    // If the old closure held resources, they'd be released here during the drop.
    let mut write_guard = aarc.spinˢ::<BoxFnMutI32> (100, Box::new ({
      let mut counter = 0;
      move || {
        counter += 1;
        counter}})) .unwrap();

    // FnMut closures need AWriteGuard (DerefMut gives &mut self)
    assert_eq! (write_guard(), 1);
    assert_eq! (write_guard(), 2);}

  trait Animal: Send + Sync + 'static {
    fn speak (&self) -> &'static str;
    fn as_any (&self) -> &dyn Any;}

  struct Dog;
  impl Animal for Dog {
    fn speak (&self) -> &'static str {"woof"}
    fn as_any (&self) -> &dyn Any {self}}

  struct Cat;
  impl Animal for Cat {
    fn speak (&self) -> &'static str {"meow"}
    fn as_any (&self) -> &dyn Any {self}}

  #[test] fn trait_swapping() {
    let aarc: AArc = AArc::none();

    let _ = aarc.spiniʳ::<Dog> (100, &mut || {
      Re::Ok (Dog)}) .unwrap();

    { let guard = aarc.spin_rd::<Dog>().unwrap().map (|d| d as &dyn Animal);
      assert_eq! (guard.speak(), "woof")}

    { let guard = aarc.spin_wr::<Dog>().unwrap();
      // set drops the Dog, stores the Cat
      let guard = guard.set::<Cat> (Cat) .map (|c| c as &mut dyn Animal);
      assert_eq! (guard.speak(), "meow")}

    { let guard = aarc.spin_rd::<Cat>().unwrap().map (|c| c as &dyn Animal);
      assert_eq! (guard.speak(), "meow")}}

  struct Zoo {
    name: String,
    resident: Box<dyn Animal>}

  #[test] fn zoo_map_to_field() {
    // map projects a guard onto a specific field of the stored struct
    let aarc: AArc = AArc::none();
    let _ = aarc.spin_set (Zoo {
      name: String::from ("City Zoo"),
      resident: Box::new (Dog)}) .unwrap();

    // AReadGuard::map → &String (name field)
    let guard = aarc.spin_rd::<Zoo>().unwrap();
    let name_guard = guard.map (|zoo| &zoo.name);
    assert_eq! (&*name_guard, "City Zoo");
    drop (name_guard);

    // AReadGuard::map → &dyn Animal (resident field, through Box Deref)
    let guard = aarc.spin_rd::<Zoo>().unwrap();
    let animal_guard = guard.map (|zoo| &*zoo.resident);
    assert_eq! (animal_guard.speak(), "woof");
    drop (animal_guard);

    // AWriteGuard::map → &mut String (mutate name in-place)
    let guard = aarc.spin_wr::<Zoo>().unwrap();
    let mut name_guard = guard.map (|zoo| &mut zoo.name);
    name_guard.push_str (" (renovated)");
    drop (name_guard);

    let guard = aarc.spin_rd::<Zoo>().unwrap();
    assert_eq! (guard.name, "City Zoo (renovated)")}

  #[test] fn zoo_write_map_swap_resident() {
    // AWriteGuard::map + DerefMut swaps a trait-object field in-place
    let aarc: AArc = AArc::none();
    let _ = aarc.spin_set (Zoo {
      name: String::from ("Safari"),
      resident: Box::new (Cat)}) .unwrap();

    // Project write guard to resident field, swap Cat→Dog
    let guard = aarc.spin_wr::<Zoo>().unwrap();
    let mut resident_guard = guard.map (|zoo| &mut zoo.resident);
    assert_eq! (resident_guard.speak(), "meow");
    *resident_guard = Box::new (Dog);
    assert_eq! (resident_guard.speak(), "woof");
    drop (resident_guard);

    // Other fields untouched; only resident changed
    let guard = aarc.spin_rd::<Zoo>().unwrap();
    assert_eq! (guard.resident.speak(), "woof");
    assert_eq! (guard.name, "Safari")}

  #[test] fn zoo_try_map_downcast() {
    let aarc: AArc = AArc::none();
    aarc.spin_set (Cat) .unwrap();

    // Read as Cat, then map to trait object `dyn Animal`
    let guard = aarc.spin_rd::<Cat>().unwrap();
    let animal_guard = guard.map (|c| c as &dyn Animal);
    assert_eq! (animal_guard.speak(), "meow");

    // Successfully downcast Animal to Cat
    let Ok (cat_guard) = animal_guard.try_map (|a| {
      a.as_any().downcast_ref::<Cat>().ok_or ("not a cat")
    }) else {panic!()};
    assert_eq! (cat_guard.speak(), "meow");

    // Fail to downcast Cat to Dog
    let Err ((cat_guard, err)) = cat_guard.try_map (|c| {
      (c as &dyn Any) .downcast_ref::<Dog>().ok_or ("cat is not a dog")
    }) else {panic!()};
    assert_eq! (err, "cat is not a dog");

    // Fail to downcast Animal to Dog
    let animal_guard = cat_guard.map (|c| c as &dyn Animal);
    let Err ((recovered_animal, err)) = animal_guard.try_map (|a| {
      a.as_any().downcast_ref::<Dog>().ok_or ("cat animal is not a dog")
    }) else {panic!()};
    assert_eq! (err, "cat animal is not a dog");
    assert_eq! (recovered_animal.speak(), "meow")}

  #[test] fn zoo_try_map_write_vec() {
    let aarc: AArc = AArc::none();
    let _ = aarc.spin_set (vec! ["woof", "meow", "moo"]) .unwrap();

    // mutate first element in-place
    let guard = aarc.spin_wr::<Vec<&str>>().unwrap();
    let mut first = guard.try_map (|v| v.first_mut().ok_or ("empty")) .unwrap();
    assert_eq! (*first, "woof");
    *first = "bark";
    drop (first);

    let guard = aarc.spin_rd::<Vec<&str>>().unwrap();
    assert_eq! (guard[0], "bark");
    drop (guard);

    // Fails on empty vec, write guard returned intact
    let _ = aarc.spin_set::<Vec<&str>> (vec![]) .unwrap();
    let guard = aarc.spin_wr::<Vec<&str>>().unwrap();
    let result = guard.try_map (|v| v.first_mut().ok_or ("empty"));
    let (recovered_guard, err) = result.err().unwrap();
    assert_eq! (err, "empty");
    assert_eq! (recovered_guard.len(), 0)}

  #[test] fn take() {
    let aarc: AArc = AArc::none();
    assert! (aarc.is_none());
    let _ = aarc.spid::<i32>().unwrap();
    assert! (aarc.is_some());

    let guard = aarc.spin_rd::<i32>().unwrap();
    assert_eq! (*guard, 0);
    drop (guard);

    let val = aarc.take(100).unwrap();  // Takes stored i32, sets EMPTY_BIT; control block stays allocated/connected.
    assert! (val.is_some());
    assert! (aarc.is_none());
    assert_eq! (aarc.status(), (0, "empty"));  // Taken state has no active locks.

    // Reads spin-out while empty (EMPTY_BIT set, not null pointer).
    let err = aarc.spinʳ::<i32> (10) .err().unwrap();
    assert_eq! (err, AArcErr::SpinOut);

    // But it can be reinitialized in-place.
    let guard = aarc.spid::<i32>().unwrap();
    assert! (aarc.is_some());
    assert_eq! (*guard, 0);}

  #[test] fn clone_after_take_stays_connected() {
    let aarc: AArc = AArc::none();
    let _ = aarc.spin_set (1i32) .unwrap();

    // Taking makes the slot empty (EMPTY_BIT) but does not detach/clear ptr
    aarc.take(100).unwrap();

    // `clone()` remains connected because ptr is non-null
    let clone = aarc.clone();

    // Empty means "no current value", so reads spin-out until reinit/set
    let err = clone.spinʳ::<i32> (10) .err().unwrap();
    assert_eq! (err, AArcErr::SpinOut);

    // Reinitialize through clone...
    let _ = clone.spin_set (7i32) .unwrap();
    // ...and observe from original: same shared control block.
    let guard = aarc.spin_rd::<i32>().unwrap();
    assert_eq! (*guard, 7)}

  fn catch_unwind_silent<F: FnOnce() -> R + UnwindSafe, R> (f: F) -> thread::Result<R> {
    let prev_hook = panic::take_hook();
    panic::set_hook (Box::new (|_| {}));
    let res = panic::catch_unwind (f);
    panic::set_hook (prev_hook);
    res}

  #[test] fn take_on_panic() {
    let aarc: AArc = AArc::none();
    let _ = aarc.spid::<i32>().unwrap();

    let res = catch_unwind_silent (|| {
      let _guard = aarc.spin_wr::<i32>().unwrap();
      panic! ("test panic");});
    // Unwind: AWriteGuard::drop detects panicking()==true, drops data, sets EMPTY_BIT.

    assert! (res.is_err());

    // Unlike std::Mutex, no poisoning — just dropped. AArc is now empty, not broken.
    assert_eq! (aarc.status(), (0, "empty"));  // Write lock is cleared during panic unwind.
    let err = aarc.spinʳ::<i32> (10) .err().unwrap();
    assert_eq! (err, AArcErr::SpinOut);

    // Can be reinitialized normally after panic
    let guard = aarc.spid::<i32>().unwrap();
    assert_eq! (*guard, 0);}

  // A type whose drop panics. Dangerous: if this drop runs during unwind
  // (i.e., while already panicking), it triggers a double-panic → process abort.
  // catch_unwind_silent isolates each test so we only ever single-panic into
  // the catch, and InitGuard's cleanup finds None (data already .take()n).
  struct PanicOnDrop;
  impl Drop for PanicOnDrop {
    fn drop (&mut self) {
      panic! ("PanicOnDrop");}}

  #[test] fn write_bit_stuck_on_panic() {
    let aarc: AArc = AArc::none();
    let _ = aarc.spin_set (PanicOnDrop) .unwrap();

    let res = catch_unwind_silent (|| {
      // spin_set acquires WRITE_BIT, .take()s old value, stores 42i32,
      // then drop(old) panics. InitGuard is live on the stack: during
      // unwind it clears WRITE_BIT|sets EMPTY_BIT. Data was already
      // .take()n, so InitGuard's drop finds None — no double-panic.
      let _ = aarc.spin_set (42i32);});

    assert! (res.is_err());

    // InitGuard cleared WRITE_BIT despite the panic, so AArc is usable
    let guard = aarc.spin_set (42i32) .unwrap();
    assert_eq! (*guard, 42);}

  #[test] fn take_stuck_on_panic() {
    let aarc: AArc = AArc::none();
    let _ = aarc.spin_set (PanicOnDrop) .unwrap();

    let res = catch_unwind_silent (|| {
      // take acquires WRITE_BIT, .take()s the value, then drop(old)
      // panics from PanicOnDrop. InitGuard unwinds: data already .take()n
      // so cleanup finds None (no second PanicOnDrop drop → no abort).
      let _ = aarc.take(100);});

    assert! (res.is_err());

    // Same guarantee: WRITE_BIT cleared, AArc still usable
    let guard = aarc.spin_set (42i32) .unwrap();
    assert_eq! (*guard, 42);}

  #[bench] fn bench_spin_rd (b: &mut test::Bencher) {
    let aarc: AArc = AArc::none();
    let _ = aarc.spid::<i32>().unwrap();
    b.iter (|| {
      let guard = aarc.spin_rd::<i32>().unwrap();
      test::black_box (*guard);});}

  #[bench] fn bench_spin_wr (b: &mut test::Bencher) {
    let aarc: AArc = AArc::none();
    let _ = aarc.spid::<i32>().unwrap();
    b.iter (|| {
      let mut guard = aarc.spin_wr::<i32>().unwrap();
      *guard = test::black_box (*guard + 1);});}

  #[bench] fn bench_clone (b: &mut test::Bencher) {
    let aarc: AArc = AArc::none();
    let _ = aarc.spid::<i32>().unwrap();
    b.iter (|| {
      test::black_box (aarc.clone());});}

  #[bench] fn bench_arc_mutex_read (b: &mut test::Bencher) {
    let m = Arc::new (Mutex::new (0i32));
    b.iter (|| {
      let guard = m.lock().unwrap();
      test::black_box (*guard);});}

  #[bench] fn bench_arc_mutex_write (b: &mut test::Bencher) {
    let m = Arc::new (Mutex::new (0i32));
    b.iter (|| {
      let mut guard = m.lock().unwrap();
      *guard = test::black_box (*guard + 1);});}

  #[bench] fn bench_arc_rwlock_read (b: &mut test::Bencher) {
    let m = Arc::new (RwLock::new (0i32));
    b.iter (|| {
      let guard = m.read().unwrap();
      test::black_box (*guard);});}

  #[bench] fn bench_arc_rwlock_write (b: &mut test::Bencher) {
    let m = Arc::new (RwLock::new (0i32));
    b.iter (|| {
      let mut guard = m.write().unwrap();
      *guard = test::black_box (*guard + 1);});}

  #[bench] fn bench_spin_set_closure (b: &mut test::Bencher) {
    let aarc: AArc = AArc::none();
    let _ = aarc.spid::<i32>().unwrap();

    // spin_set can store closures that return Result
    let guard = aarc.spin_set::<BoxFnReI32> (Box::new (|| Ok (42))) .unwrap();
    assert_eq! (guard().unwrap(), 42);  // Callable through AWriteGuard.
    drop (guard);

    let read_guard = aarc.spin_rd::<BoxFnReI32>().unwrap();
    assert_eq! (read_guard().unwrap(), 42);  // Callable through AReadGuard too (Fn).
    drop (read_guard);

    let mut counter = 0u32;
    let guard = aarc.spin_set::<BoxFnMutReU32> (Box::new (move || {
      counter += 1;
      Ok (counter)})) .unwrap();
    drop (guard);

    // FnMut: needs AWriteGuard for stateful calls
    let mut write_guard = aarc.spin_wr::<BoxFnMutReU32>().unwrap();
    assert_eq! (write_guard().unwrap(), 1);
    assert_eq! (write_guard().unwrap(), 2);
    drop (write_guard);

    b.iter (|| {
      let mut guard = aarc.spin_wr::<BoxFnMutReU32>().unwrap();
      let mut c = guard().unwrap();
      let is_odd = c % 2 != 0;
      let next: BoxFnMutReU32 = Box::new (move || {
        c += 1;
        Ok (c)});
      // Alternates between spin_set (drop + create) and set (in-place swap)
      if is_odd {
        drop (guard);
        test::black_box (aarc.spin_set::<BoxFnMutReU32> (next) .unwrap());}
      else {
        test::black_box (guard.set::<BoxFnMutReU32> (next));}});}

  #[bench] fn bench_spin_wait_for_type (b: &mut test::Bencher) {
    let aarc: AArc = AArc::none();
    let _ = aarc.spid::<i32>().unwrap();

    let aarc_clone = aarc.clone();
    let handle = thread::spawn (move || {
      loop {
        // Spins until the value is u32 (type-aware spinning)
        let guard = aarc_clone.spin_wr::<u32>().unwrap();
        if *guard == 999 {break;}
        test::black_box (*guard);
        guard.set::<i32> (0i32);}});  // Swap back to i32 for the other thread.

    b.iter (|| {
      // This thread writes i32 → u32, the other writes u32 → i32
      let guard = aarc.spin_wr::<i32>().unwrap();
      test::black_box (guard.set::<u32> (42u32));});

    let guard = aarc.spin_wr::<i32>().unwrap();
    guard.set::<u32> (999u32);  // Sentinel to stop the other thread.
    handle.join().unwrap();}

  #[test] fn inner_value_dropped_once() {
    struct DropCounter (Arc<AtomicUsize>);
    impl Drop for DropCounter {
      fn drop (&mut self) {
        self.0.fetch_add (1, Ordering::Relaxed);}}
    let counter = Arc::new (AtomicUsize::new (0));
    // Dropping the last AArc drops the control block, which drops the inner value.
    // count!=1 would mean double-free (unsound) or leak (resource bug).
    { let aarc: AArc = AArc::none();
      let _ = aarc.spin_set (DropCounter (counter.clone())) .unwrap();
    }  // AArc dropped: refcount 1→0, fence(Acquire), Box::from_raw frees ControlBlock + data.
    assert_eq! (counter.load (Ordering::Relaxed), 1);}

  #[test] fn benign_read_guard_drop() {
    let aarc: AArc = AArc::none();
    let _ = aarc.spid::<i32>().unwrap();
    // Multiple AReadGuards can coexist (shared read access)
    { let guard1 = aarc.spin_rd::<i32>().unwrap();
      let guard2 = aarc.spin_rd::<i32>().unwrap();
      assert_eq! (aarc.status(), (2, ""));  // Two active readers.
      assert_eq! (*guard1, 0);
      assert_eq! (*guard2, 0); }
    assert_eq! (aarc.status(), (0, ""));  // Both readers dropped.
    // If AReadGuard::drop failed to clear READ_INC, this would spin-out
    let mut write_guard = aarc.spin_wr::<i32>().unwrap();
    assert_eq! (aarc.status(), (0, "write-locked"));  // One active writer.
    *write_guard = 42;
    assert_eq! (*write_guard, 42);}

  #[test] fn benign_write_guard_drop() {
    let aarc: AArc = AArc::none();
    let _ = aarc.spid::<i32>().unwrap();
    { let mut write_guard = aarc.spin_wr::<i32>().unwrap();
      *write_guard = 99; }  // AWriteGuard dropped here, releases exclusive lock.
    // If AWriteGuard::drop failed to clear WRITE_BIT, this would spin-out
    let read_guard = aarc.spin_rd::<i32>().unwrap();
    assert_eq! (*read_guard, 99);}

  #[test] fn benign_clone_drops() {
    let aarc: AArc = AArc::none();
    let _ = aarc.spin_set (String::from ("hello")) .unwrap();
    // Clones share the same control block whenever ptr is non-null (including taken/EMPTY_BIT states)
    let clone1 = aarc.clone();
    let clone2 = aarc.clone();
    drop (clone1);  // Refcount 3→2; data untouched, only ref bookkeeping.
    { let guard = clone2.spin_rd::<String>().unwrap();
      assert_eq! (*guard, "hello");}
    drop (aarc);  // Refcount 2→1; control block + String still alive for clone2.
    { let guard = clone2.spin_rd::<String>().unwrap();
      assert_eq! (*guard, "hello");}}  // clone2 dropped: refcount 1→0, String deallocated.

  #[test] fn upgrade_downgrade() {
    let aarc: AArc = AArc::none();
    let _ = aarc.spid::<i32>().unwrap();
    let read_guard = aarc.spin_rd::<i32>().unwrap();
    assert_eq! (*read_guard, 0);
    assert_eq! (aarc.status(), (1, ""));
    // upgrade converts AReadGuard to AWriteGuard without downcasting
    let mut write_guard = read_guard.wr().unwrap();
    assert_eq! (aarc.status(), (0, "write-locked"));
    *write_guard = 42;
    // downgrade converts AWriteGuard to AReadGuard without downcasting
    let read_guard2 = write_guard.rd();
    assert_eq! (aarc.status(), (1, ""));
    assert_eq! (*read_guard2, 42)}

  #[test] fn typed_aarc() {
    let aarc = AArc::<i32>::none();
    assert_eq! (fomat! ([aarc]), "AArc { readers: 0, status: \"null\" }");
    let mut guard = aarc.spidʷ (100) .unwrap();
    assert_eq! (*guard, 0);
    assert_eq! (fomat! ([aarc]), "AArc { readers: 0, status: \"write-locked\", data: <locked or empty> }");
    *guard = 42;
    let read_guard = guard.rd();
    assert_eq! (*read_guard, 42);
    assert_eq! (fomat! ([aarc]), "AArc { readers: 1, data: 42 }");
    drop (read_guard);
    aarc.take(100).unwrap();
    assert_eq! (fomat! ([aarc]), "AArc { readers: 0, status: \"empty\" }")}

  #[test] fn upgrade_spin_out() {
    let aarc: AArc = AArc::none();
    let _ = aarc.spid::<i32>().unwrap();
    let read_guard1 = aarc.spin_rd::<i32>().unwrap();
    let read_guard2 = aarc.spin_rd::<i32>().unwrap();
    // upgradeᵗ fails if there are other active readers, returning the original AReadGuard
    let (recovered_guard, err) = read_guard1.wrᵗ (10) .err().unwrap();
    assert_eq! (err, AArcErr::SpinOut);
    assert_eq! (aarc.status(), (2, ""));
    assert_eq! (*recovered_guard, 0);
    drop (recovered_guard);
    drop (read_guard2);
    assert_eq! (aarc.status(), (0, ""))}

  #[test] fn conditional_spins() {
    let aarc = AArc::<i32>::none();
    let _ = aarc.spin_set (0) .unwrap();

    // spicʳ: condition immediately true → read guard
    let guard = aarc.spicʳ (-1, &mut |v| Re::Ok (*v == 0)) .unwrap();
    assert_eq! (*guard, 0);
    drop (guard);

    // spicʳ: condition always false → spin-out
    let mut runs = 0;
    let err = aarc.spicʳ (-4, &mut |v| {runs += 1; Re::Ok (100 < *v)}) .err().unwrap();
    assert_eq! (err, AArcErr::SpinOut);
    assert_eq! (runs, 3);

    // spicʳ: condition error → propagated as AArcErr::Init
    runs = 0;
    let err = aarc.spicʳ (-1, &mut |_| {runs += 1; fail! ("cond err")}) .err().unwrap();
    match err {
      AArcErr::Init (msg) => assert! (msg.ends_with ("] cond err")),
      _ => panic! ("Expected AArcErr::Init")}
    assert_eq! (runs, 1);

    // spicʷ: condition true → write guard, mutate
    runs = 0;
    let mut guard = aarc.spicʷ (-3, &mut |v| {runs += 1; Re::Ok (*v == 0)}) .unwrap();
    *guard = 42;
    drop (guard);
    assert_eq! (runs, 1);

    // spicʷ: condition false (value changed) → spin-out
    runs = 0;
    let err = aarc.spicʷ (-1, &mut |v| {runs += 1; Re::Ok (*v == 0)}) .err().unwrap();
    assert_eq! (err, AArcErr::SpinOut);
    assert_eq! (runs, 2);

    // Cross-thread: writer updates value, conditional reader waits with negative spins
    let aarc2 = AArc::<i32>::none();
    let _ = aarc2.spin_set (0) .unwrap();
    let clone = aarc2.clone();
    let handle = thread::spawn (move || {
      loop {
        thread::sleep (Duration::from_millis (10));
        let mut guard = clone.spin_wr().unwrap();
        *guard += 1;
        if *guard == 30 {break}}});

    // Positive 30 spins 30 times in one burst, too fast to observe v 20
    runs = 0;
    let guard = aarc2.spicʳ (30, &mut |v| {runs += 1; Re::Ok (20 <= *v)});
    assert! (guard.is_err());
    assert_eq! (runs, 30);

    // Negative -30 spins for ~30 centiseconds; condition re-checked once per 30ms sleep cycle
    runs = 0;
    let guard = aarc2.spicʳ (-30, &mut |v| {runs += 1; Re::Ok (20 <= *v)}) .unwrap();
    assert! (20 <= *guard);
    print! ("v {} in {} checks; ", *guard, runs);
    assert! (6 <= runs && runs <= 12, "{}", runs);
    drop (guard);
    handle.join().unwrap();}

  #[test] fn empty_connected_channel() {
    let aarc = AArc::<i32>::empty();
    assert! (aarc.is_none());
    let clone = aarc.clone();

    let handle = thread::spawn (move || {
      thread::sleep (Duration::from_millis (10));
      let _ = clone.spin_set (42) .unwrap();});

    // spin_rd will spin until EMPTY_BIT is cleared
    let guard = aarc.spinʳ (-100) .unwrap();
    assert_eq! (*guard, 42);
    handle.join().unwrap();}}
