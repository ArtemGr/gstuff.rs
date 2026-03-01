//! ### `AArc` Methods
//! * `const fn none() -> Self` Creates empty, uninitialized `AArc`. Ideal for `static` declarations.
//! * `fn new<T> (val: T) -> Self` Creates new `AArc` initialized with given value.
//! * `fn is_none (&self) -> bool` Returns `true` if empty or evicted.
//! * `fn is_some (&self) -> bool` Returns `true` if currently holding a value.
//! * `fn clone (&self) -> Self` Clones `AArc`, disconnected if empty.
//! * `fn cloneᵗ (&self, spins: u32) -> Result<Self, AArcErr>`
//!   Clones `AArc`, returning error if out of spins or on disconnect.
//! * `fn evict / evictᵗ (&self) -> Result<(), AArcErr>` Evicts stored value, resetting `AArc` to empty.
//! * `fn spin_init / spiniʳ<T> (&self, init: &mut dyn FnMut() -> Re<T>) -> Result<AReadGuard<'_, T>, AArcErr>`
//!   Initializes `AArc` if empty, returns read guard. Spins if downcast fails.
//! * `fn spin_default / spidʳ<T> (&self) -> Result<AReadGuard<'_, T>, AArcErr>`
//!   Initializes with `T::default()` if empty. Spins if downcast fails.
//! * `fn spidʷ<T> (&self, spins: u32) -> Result<AWriteGuard<'_, T>, AArcErr>`
//!   Initializes with `T::default()` if empty, returning a write guard. Spins if downcast fails.
//! * `fn spin_read / spinʳ<T> (&self) -> Result<AReadGuard<'_, T>, AArcErr>`
//!   Acquires read lock and downcasts to `T`. Spins if downcast fails.
//! * `fn spin_write / spinʷ<T> (&self) -> Result<AWriteGuard<'_, T>, AArcErr>`
//!   Acquires exclusive write lock and downcasts to `T`. Spins if downcast fails.
//! * `fn spin_set / spinˢ<T> (&self, val: T) -> Result<AWriteGuard<'_, T>, AArcErr>`
//!   Acquires write lock and sets new value of type `T`, returning typed guard.
//! * `fn status (&self) -> (u32, &'static str)` Returns `(read_locks, status_string)`.
//!
//! ### Guard Methods
//! * `AReadGuard::aarc (&self) -> AArc` Recovers new `AArc` reference from read guard.
//! * `AReadGuard::upgrade / upgradeᵗ (self) -> Result<AWriteGuard<'_, T>, (Self, AArcErr)>`
//!   Upgrades read lock to write lock without downcasting.
//! * `AWriteGuard::aarc (&self) -> AArc` Recovers new `AArc` reference from write guard.
//! * `AWriteGuard::set<U> (self, val: U) -> AWriteGuard<'_, U>`
//!   Replaces stored value with new type `U` and returns new typed guard.
//! * `AWriteGuard::evict (self)` Evicts stored value while holding write lock.
//!
//! If a thread panics while holding a `AWriteGuard`, the stored data is
//! evicted (`drop`ped) rather than poisoned. Other threads will see the `AArc` as empty.
//! `AReadGuard`s are safe to drop during a panic; they simply release the read lock.
//! Leaking guards (e.g., via `std::mem::forget`) will permanently
//! lock the `AArc`, preventing future reads or writes.

use crate::{pause_yield, SPIN_OUT};
use crate::re::Re;
use std::any::Any;
use std::cell::UnsafeCell;
use std::hint::spin_loop;
use std::marker::PhantomData;
use std::mem::forget;
use std::ops::{Deref, DerefMut};
use std::ptr;
use std::sync::atomic::{fence, AtomicPtr, AtomicU32, Ordering};
use std::thread::panicking;

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

/// Atomic, type-erased, shared mutable container.
///
/// Stores a `dyn Any` behind a spinlock-based RwLock. Lock acquisition performs
/// atomic CAS + `Any::downcast`; the returned guards hold a direct raw pointer
/// to `T`, so subsequent access is zero-cost C-like pointer dereference.
pub struct AArc {
  ptr: AtomicPtr<ControlBlock>}

struct ControlBlock {
  state: AtomicU32,
  data: UnsafeCell<Option<Box<dyn Any + Send + Sync>>>}

impl ControlBlock {
  fn replace_data<T: Send + Sync + 'static> (&self, val: T) -> *mut T {
    let mut b = Box::new (val);
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

unsafe impl Send for AArc {}
unsafe impl Sync for AArc {}

impl Clone for AArc {
  /// Clones the AArc.
  ///
  /// Disconnected when instance is completely uninitialized (e.g., from `AArc::none()` before first init).
  /// Evicted (`EMPTY_BIT`) instances stay connected.
  fn clone (&self) -> Self {
    let ptr = self.ptr.load (Ordering::Acquire);
    if !ptr.is_null() {
      let cb = unsafe {&*ptr};
      let old = cb.state.fetch_add (REF_INC, Ordering::Relaxed);
      if (old & REF_MASK) == REF_MASK {panic! ()}}
    AArc {ptr: AtomicPtr::new (ptr)}}}

impl Drop for AArc {
  fn drop (&mut self) {
    let ptr = self.ptr.load (Ordering::Acquire);
    if !ptr.is_null() {
      let cb = unsafe {&*ptr};
      let old = cb.state.fetch_sub (REF_INC, Ordering::Release);
      if (old & REF_MASK) == REF_INC {
        fence (Ordering::Acquire);
        debug_assert! ((old & (READ_MASK | WRITE_BIT)) == 0, "Active guards during AArc drop!");
        unsafe {let _ = Box::from_raw (ptr);}}}}}

impl Default for AArc {
  fn default() -> Self {
    Self::none()}}

impl AArc {
  pub const fn none() -> Self {
    AArc {ptr: AtomicPtr::new (ptr::null_mut())}}
  
  /// Returns `true` if the `AArc` is uninitialized or its value has been evicted.
  pub fn is_none (&self) -> bool {
    let ptr = self.ptr.load (Ordering::Acquire);
    if ptr.is_null() {return true}
    let cb = unsafe {&*ptr};
    (cb.state.load (Ordering::Relaxed) & EMPTY_BIT) != 0}

  /// Returns `true` if the `AArc` currently holds an initialized value.
  pub fn is_some (&self) -> bool {
    !self.is_none()}

  fn try_alloc_cb (&self) -> Option<*mut ControlBlock> {
    let cb = Box::into_raw (Box::new (ControlBlock {
      state: AtomicU32::new (REF_INC | WRITE_BIT | EMPTY_BIT),
      data: UnsafeCell::new (None)}));
    match self.ptr.compare_exchange (ptr::null_mut(), cb, Ordering::Release, Ordering::Acquire) {
      Ok (_) => Some (cb),
      Err (_) => {
        unsafe {let _ = Box::from_raw (cb);}
        None}}}

  pub fn new<T: Send + Sync + 'static> (val: T) -> Self {
    let cb = Box::into_raw (Box::new (ControlBlock {
      state: AtomicU32::new (REF_INC),
      data: UnsafeCell::new (Some (Box::new (val)))}));
    AArc {ptr: AtomicPtr::new (cb)}}
  
  /// Clones the AArc, returning an error if out of spins or if would disconnect.
  pub fn cloneᵗ (&self, spins: u32) -> Result<Self, AArcErr> {
    for spin in 0..spins {
      let ptr = self.ptr.load (Ordering::Acquire);
      if !ptr.is_null() {
        let cb = unsafe {&*ptr};
        let state = cb.state.load (Ordering::Acquire);
        if (state & REF_MASK) == REF_MASK {return Err (AArcErr::RefcountOverflow)}
        if cb.state.compare_exchange_weak (state, state + REF_INC, Ordering::Relaxed, Ordering::Relaxed) .is_ok() {
          return Ok (AArc {ptr: AtomicPtr::new (ptr)})}
        continue}
      if spin % 10 == 0 {spin_loop()} else {pause_yield()}}
    Err (AArcErr::Disconnect)}

  pub fn evictᵗ (&self, spins: u32) -> Result<(), AArcErr> {
    for spin in 0..spins {
      let ptr = self.ptr.load (Ordering::Acquire);
      if ptr.is_null() {return Ok (())}
      let cb = unsafe {&*ptr};
      let state = cb.state.load (Ordering::Acquire);
      if state & WRITE_BIT == 0 && state & READ_MASK == 0 {
        if cb.state.compare_exchange_weak (state, state | WRITE_BIT, Ordering::Acquire, Ordering::Relaxed) .is_ok() {
          let mut guard = InitGuard {cb: ptr, success: false, _marker: PhantomData};
          let old = unsafe {(*cb.data.get()).take()};
          drop (old);
          guard.success = true;
          let mut current = cb.state.load (Ordering::Relaxed);
          loop {
            let new = (current | EMPTY_BIT) & !WRITE_BIT;
            match cb.state.compare_exchange_weak (current, new, Ordering::Release, Ordering::Relaxed) {
              Ok (_) => return Ok (()),
              Err (x) => current = x}}}
        continue}
      if spin % 10 == 0 {spin_loop()} else {pause_yield()}}
    Err (AArcErr::SpinOut)}

  pub fn evict (&self) -> Result<(), AArcErr> {
    self.evictᵗ (unsafe {SPIN_OUT})}

  pub fn spiniʳ<T: Send + Sync + 'static> (&self, spins: u32, init: &mut dyn FnMut() -> Re<T>)
  -> Result<AReadGuard<'_, T>, AArcErr> {
    for spin in 0..spins {
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
      if spin % 10 == 0 {spin_loop()} else {pause_yield()}}
    Err (AArcErr::SpinOut)}

  fn do_init<T: Send + Sync + 'static> (&self, cb_ptr: *mut ControlBlock, init: &mut dyn FnMut() -> Re<T>)
  -> Result<AReadGuard<'_, T>, AArcErr> {
    let mut guard = InitGuard {cb: cb_ptr, success: false, _marker: PhantomData};
    match init() {
      Re::Ok (val) => {
        let cb = unsafe {&*cb_ptr};
        let ptr = cb.replace_data (val) as *const T;
        guard.success = true;

        let mut current = cb.state.load (Ordering::Relaxed);
        loop {
          let new = (current & !WRITE_BIT & !EMPTY_BIT) + READ_INC;
          match cb.state.compare_exchange_weak (current, new, Ordering::Release, Ordering::Relaxed) {
            Ok (_) => break, Err (x) => current = x}}
        Ok (AReadGuard {cb, ptr, _phantom: PhantomData})}
      Re::Err (e) => Err (AArcErr::Init (e))}}

  pub fn spidʳ<T: Default + Send + Sync + 'static> (&self, spins: u32) -> Result<AReadGuard<'_, T>, AArcErr> {
    self.spiniʳ (spins, &mut || Re::Ok (T::default()))}

  pub fn spin_init<T: Send + Sync + 'static> (&self, init: &mut dyn FnMut() -> Re<T>) -> Result<AReadGuard<'_, T>, AArcErr> {
    self.spiniʳ (unsafe {SPIN_OUT}, init)}

  pub fn spin_default<T: Default + Send + Sync + 'static> (&self) -> Result<AReadGuard<'_, T>, AArcErr> {
    self.spidʳ (unsafe {SPIN_OUT})}

  pub fn spidʷ<T: Default + Send + Sync + 'static> (&self, spins: u32) -> Result<AWriteGuard<'_, T>, AArcErr> {
    for spin in 0..spins {
      let ptr = self.ptr.load (Ordering::Acquire);
      if ptr.is_null() {
        if let Some (cb_ptr) = self.try_alloc_cb() {
          let mut guard = InitGuard {cb: cb_ptr, success: false, _marker: PhantomData};
          let cb = unsafe {&*cb_ptr};
          let data_ptr = cb.replace_data (T::default());
          cb.state.fetch_and (!EMPTY_BIT, Ordering::Release);
          guard.success = true;
          return Ok (AWriteGuard {cb, ptr: data_ptr, _phantom: PhantomData})
        } else {continue}
      } else {
        let cb = unsafe {&*ptr};
        let state = cb.state.load (Ordering::Acquire);
        if state & WRITE_BIT == 0 && state & READ_MASK == 0 {
          if state & EMPTY_BIT != 0 {
            if cb.state.compare_exchange_weak (state, state | WRITE_BIT, Ordering::Acquire, Ordering::Relaxed) .is_ok() {
              let mut guard = InitGuard {cb: ptr, success: false, _marker: PhantomData};
              let data_ptr = cb.replace_data (T::default());
              cb.state.fetch_and (!EMPTY_BIT, Ordering::Release);
              guard.success = true;
              return Ok (AWriteGuard {cb: ptr, ptr: data_ptr, _phantom: PhantomData})}
          } else {
            if cb.state.compare_exchange_weak (state, state | WRITE_BIT, Ordering::Acquire, Ordering::Relaxed) .is_ok() {
              let data_mut = unsafe {&mut *cb.data.get()};
              if let Some (any_box) = data_mut {
                if let Some (typed_mut) = any_box.downcast_mut::<T>() {
                  return Ok (AWriteGuard {cb: ptr, ptr: typed_mut as *mut T, _phantom: PhantomData})}}
              cb.state.fetch_and (!WRITE_BIT, Ordering::Release);}
            else {continue}}}
      }
      if spin % 10 == 0 {spin_loop()} else {pause_yield()}}
    Err (AArcErr::SpinOut)}

  pub fn spinʳ<T: 'static> (&self, spins: u32) -> Result<AReadGuard<'_, T>, AArcErr> {
    // All expensive work (atomic CAS, downcast) happens here.
    // The returned AReadGuard holds *const T — zero-cost deref after this point.
    for spin in 0..spins {
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
      if spin % 10 == 0 {spin_loop()} else {pause_yield()}}
    Err (AArcErr::SpinOut)}

  pub fn spin_read<T: 'static> (&self) -> Result<AReadGuard<'_, T>, AArcErr> {
    self.spinʳ (unsafe {SPIN_OUT})}

  pub fn spinʷ<T: 'static> (&self, spins: u32) -> Result<AWriteGuard<'_, T>, AArcErr> {
    // All expensive work (atomic CAS, downcast) happens here.
    // The returned AWriteGuard holds *mut T — zero-cost deref after this point.
    for spin in 0..spins {
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
      if spin % 10 == 0 {spin_loop()} else {pause_yield()}}
    Err (AArcErr::SpinOut)}

  pub fn spin_write<T: 'static> (&self) -> Result<AWriteGuard<'_, T>, AArcErr> {
    self.spinʷ (unsafe {SPIN_OUT})}

  pub fn spinˢ<T: Send + Sync + 'static> (&self, spins: u32, val: T) -> Result<AWriteGuard<'_, T>, AArcErr> {
    for spin in 0..spins {
      let ptr = self.ptr.load (Ordering::Acquire);
      if ptr.is_null() {
        if let Some (cb_ptr) = self.try_alloc_cb() {
          // InitGuard ensures cleanup if any operation panics before we return the AWriteGuard
          let mut guard = InitGuard {cb: cb_ptr, success: false, _marker: PhantomData};
          let cb = unsafe {&*cb_ptr};
          let data_ptr = cb.replace_data (val);
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
            let data_ptr = cb.replace_data (val);
            cb.state.fetch_and (!EMPTY_BIT, Ordering::Release);
            guard.success = true;
            return Ok (AWriteGuard {cb, ptr: data_ptr, _phantom: PhantomData})}
          continue}}
      if spin % 10 == 0 {spin_loop()} else {pause_yield()}}
    Err (AArcErr::SpinOut)}

  pub fn spin_set<T: Send + Sync + 'static> (&self, val: T) -> Result<AWriteGuard<'_, T>, AArcErr> {
    self.spinˢ (unsafe {SPIN_OUT}, val)}

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

struct InitGuard<'a> {
  cb: *mut ControlBlock,
  success: bool,
  _marker: PhantomData<&'a ()>}

impl<'a> Drop for InitGuard<'a> {
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
pub struct AReadGuard<'a, T> {
  cb: *const ControlBlock,
  ptr: *const T,
  _phantom: PhantomData<&'a T>}

impl<'a, T: std::fmt::Debug + 'static> std::fmt::Debug for AReadGuard<'a, T> {
  fn fmt (&self, fm: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    std::fmt::Debug::fmt (&**self, fm)}}

impl<'a, T: 'static> Deref for AReadGuard<'a, T> {
  type Target = T;
  fn deref (&self) -> &T {
    // Zero-cost: raw pointer deref, no atomics or downcast.
    unsafe {&*self.ptr}}}

impl<'a, T> AReadGuard<'a, T> {
  pub fn aarc (&self) -> AArc {
    let cb = unsafe {&*self.cb};
    let old = cb.state.fetch_add (REF_INC, Ordering::Relaxed);
    if (old & REF_MASK) == REF_MASK {panic! ()}
    AArc {ptr: AtomicPtr::new (self.cb as *mut _)}}

  /// Attempts to upgrade the read lock to a write lock without downcasting.
  /// 
  /// **Warning:** If two threads hold read locks and both attempt to upgrade, 
  /// they will spin-out, as neither would release their read lock.
  /// On failure the read guard is returned in the error tuple.
  pub fn upgradeᵗ (self, spins: u32) -> Result<AWriteGuard<'a, T>, (Self, AArcErr)> {
    let cb = unsafe {&*self.cb};
    for spin in 0..spins {
      let state = cb.state.load (Ordering::Acquire);
      if (state & READ_MASK) == READ_INC {
        if cb.state.compare_exchange_weak (state, (state - READ_INC) | WRITE_BIT, Ordering::Acquire, Ordering::Relaxed) .is_ok() {
          let ptr = self.ptr as *mut T;
          let cb_ptr = self.cb;
          forget (self);
          return Ok (AWriteGuard {cb: cb_ptr, ptr, _phantom: PhantomData})}}
      if spin % 10 == 0 {spin_loop()} else {pause_yield()}}
    Err ((self, AArcErr::SpinOut))}

  pub fn upgrade (self) -> Result<AWriteGuard<'a, T>, (Self, AArcErr)> {
    self.upgradeᵗ (unsafe {SPIN_OUT})}}

impl<'a, T> Drop for AReadGuard<'a, T> {
  fn drop (&mut self) {
    let cb = unsafe {&*self.cb};
    cb.state.fetch_sub (READ_INC, Ordering::Release);}}

/// Write guard holding a direct `*mut T` obtained during lock acquisition.
pub struct AWriteGuard<'a, T> {
  cb: *const ControlBlock,
  ptr: *mut T,
  _phantom: PhantomData<&'a mut T>}

impl<'a, T: std::fmt::Debug + 'static> std::fmt::Debug for AWriteGuard<'a, T> {
  fn fmt (&self, fm: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    std::fmt::Debug::fmt (&**self, fm)}}

impl<'a, T: 'static> Deref for AWriteGuard<'a, T> {
  type Target = T;
  fn deref (&self) -> &T {
    // Zero-cost: raw pointer deref, no atomics or downcast.
    unsafe {&*self.ptr}}}

impl<'a, T: 'static> DerefMut for AWriteGuard<'a, T> {
  fn deref_mut (&mut self) -> &mut T {
    // Zero-cost: raw pointer deref, no atomics or downcast.
    unsafe {&mut *self.ptr}}}

impl<'a, T> AWriteGuard<'a, T> {
  pub fn aarc (&self) -> AArc {
    let cb = unsafe {&*self.cb};
    let old = cb.state.fetch_add (REF_INC, Ordering::Relaxed);
    if (old & REF_MASK) == REF_MASK {panic! ()}
    AArc {ptr: AtomicPtr::new (self.cb as *mut _)}}

  pub fn set<U: Send + Sync + 'static> (self, val: U) -> AWriteGuard<'a, U> {
    let cb = unsafe {&*self.cb};
    // Drop-safe: if drop(old) panics inside replace_data, `forget(self)` below has not yet run,
    // so `AWriteGuard::drop` executes during unwind. That impl checks
    // `panicking()`, takes (now-new) data, drops it, clears WRITE_BIT and
    // sets EMPTY_BIT. No InitGuard needed — AWriteGuard itself is the guard.
    let ptr = cb.replace_data (val);
    cb.state.fetch_and (!EMPTY_BIT, Ordering::Release);
    let guard = AWriteGuard {cb: self.cb, ptr, _phantom: PhantomData};
    forget (self);
    guard}
  
  pub fn evict (self) {
    let cb = unsafe {&*self.cb};
    let old = unsafe {(*cb.data.get()).take()};
    // Drop-safe: if drop(old) panics, `forget(self)` has not yet run,
    // so `AWriteGuard::drop` fires during unwind. It calls take() again
    // (gets None — no double-drop), then clears WRITE_BIT | sets EMPTY_BIT.
    // The lock cannot get stuck.
    drop (old);
    let mut current = cb.state.load (Ordering::Relaxed);
    loop {
      let new = (current | EMPTY_BIT) & !WRITE_BIT;
      match cb.state.compare_exchange_weak (current, new, Ordering::Release, Ordering::Relaxed) {
        Ok (_) => break, Err (x) => current = x}}
    forget (self)}}

impl<'a, T> Drop for AWriteGuard<'a, T> {
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
  use super::*;
  use std::panic::{self, UnwindSafe};
  use std::sync::{Arc, Mutex, RwLock};
  use std::sync::atomic::AtomicUsize;
  use std::thread;
  type BoxFnI32 = Box<dyn Fn() -> i32 + Send + Sync>;
  type BoxFnMutI32 = Box<dyn FnMut() -> i32 + Send + Sync>;
  type BoxFnReI32 = Box<dyn Fn() -> Result<i32, AArcErr> + Send + Sync>;
  type BoxFnMutReU32 = Box<dyn FnMut() -> Result<u32, AArcErr> + Send + Sync>;

  #[test] fn test_spid_w() {
    let aarc = AArc::none();
    assert! (aarc.is_none());
    assert_eq! (aarc.status(), (0, "null"));  // Empty/uninitialized has no locks.
    // spidʷ initializes with T::default() if empty, returns AWriteGuard
    let mut guard = aarc.spidʷ::<i32> (100) .unwrap();
    assert! (aarc.is_some());
    assert_eq! (aarc.status(), (0, "write-locked"));  // AWriteGuard holds the exclusive write lock.
    assert_eq! (*guard, 0);
    *guard = 42;
    drop (guard);
    assert_eq! (aarc.status(), (0, ""));  // Lock released.
    
    let read_guard = aarc.spin_read::<i32>().unwrap();
    assert_eq! (aarc.status(), (1, ""));  // AReadGuard holds a shared read lock.
    assert_eq! (*read_guard, 42)}

  #[test] fn test_spid_w_existing() {
    let aarc = AArc::none();
    let _ = aarc.spin_set (5i32) .unwrap();
    
    // spidʷ should NOT overwrite with default (0) if already initialized
    let guard = aarc.spidʷ::<i32> (100) .unwrap();
    assert_eq! (*guard, 5)}

  #[test] fn test_basic_init_and_read() {
    let aarc = AArc::none();  // start empty
    // spin_default initializes with T::default() if empty, returns AReadGuard
    let guard = aarc.spin_default::<i32>().unwrap();
    assert_eq! (aarc.status(), (1, ""));  // Snapshot shows 1 reader, 0 writers.
    assert_eq! (*guard, 0);  // AReadGuard derefs to &T.

    let recovered_aarc = guard.aarc();
    assert_eq! (recovered_aarc.status(), (1, ""));

    drop (guard);  // Must drop AReadGuard before spin_write; no reader→writer upgrade.

    // spin_write acquires exclusive write lock
    let write_guard = aarc.spin_write::<i32>().unwrap();
    assert_eq! (aarc.status(), (0, "write-locked"));  // Snapshot shows 0 readers, 1 writer.

    let recovered_aarc2 = write_guard.aarc();
    assert_eq! (recovered_aarc2.status(), (0, "write-locked"));

    // set drops the old value inside, then stores the new one (can even change type)
    let mut write_guard = write_guard.set (42i32);
    assert_eq! (*write_guard, 42);
    *write_guard = 43;  // DerefMut allows in-place mutation
    assert_eq! (*write_guard, 43);}  // AWriteGuard dropped: clears WRITE_BIT, data persists.

  #[test] fn test_re_init() {
    use crate::fail;
    use fomat_macros::fomat;

    let aarc = AArc::none();
    let err = aarc.spin_init::<i32> (&mut || {fail! ("init failed")}) .unwrap_err();
    match err {
      AArcErr::Init (msg) => assert! (msg.ends_with ("] init failed")),
      _ => panic! ("Expected AArcErr::Init")}

    let guard = aarc.spin_init::<i32> (&mut || Re::Ok (42)) .unwrap();
    assert_eq! (*guard, 42);}

  #[test] fn test_closure_storage() {
    let aarc = AArc::none();

    // spiniʳ with custom spin limit; closure-based init
    let _ = aarc.spiniʳ::<BoxFnI32> (100, &mut || {
      Re::Ok (Box::new (|| 77))}) .unwrap();

    // Fn closures callable through AReadGuard (Deref gives &self)
    let read_guard = aarc.spin_read::<BoxFnI32>().unwrap();
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
    fn speak (&self) -> &'static str;}

  struct Dog;
  impl Animal for Dog {fn speak (&self) -> &'static str {"woof"}}

  struct Cat;
  impl Animal for Cat {fn speak (&self) -> &'static str {"meow"}}

  #[test] fn test_trait_swapping() {
    let aarc = AArc::none();

    // store a trait object
    let _ = aarc.spiniʳ::<Box<dyn Animal>> (100, &mut || {
      Re::Ok (Box::new (Dog))}) .unwrap();

    { let guard = aarc.spin_read::<Box<dyn Animal>>().unwrap();
      assert_eq! (guard.speak(), "woof");}

    // Hot-swap: set replaces Dog with Cat at runtime
    { let guard = aarc.spin_write::<Box<dyn Animal>>().unwrap();
      // set drops the Dog, stores the Cat; old value dropped before new guard returned
      let guard = guard.set::<Box<dyn Animal>> (Box::new (Cat));
      assert_eq! (guard.speak(), "meow");}

    { let guard = aarc.spin_read::<Box<dyn Animal>>().unwrap();
      assert_eq! (guard.speak(), "meow");}}

  #[test] fn test_evict() {
    let aarc = AArc::none();
    assert! (aarc.is_none());
    let _ = aarc.spin_default::<i32>().unwrap();
    assert! (aarc.is_some());

    let guard = aarc.spin_read::<i32>().unwrap();
    assert_eq! (*guard, 0);
    drop (guard);

    aarc.evict().unwrap();  // Drops stored i32, sets EMPTY_BIT; control block stays allocated/connected.
    assert! (aarc.is_none());
    assert_eq! (aarc.status(), (0, "empty"));  // Evicted state has no active locks.

    // Reads spin-out while empty (EMPTY_BIT set, not null pointer).
    let err = aarc.spinʳ::<i32> (10) .err().unwrap();
    assert_eq! (err, AArcErr::SpinOut);

    // But it can be reinitialized in-place.
    let guard = aarc.spin_default::<i32>().unwrap();
    assert! (aarc.is_some());
    assert_eq! (*guard, 0);}

  #[test] fn test_clone_after_evict_stays_connected() {
    let aarc = AArc::none();
    let _ = aarc.spin_set (1i32) .unwrap();

    // Eviction makes the slot empty (EMPTY_BIT) but does not detach/clear ptr
    aarc.evict().unwrap();

    // `clone()` remains connected because ptr is non-null
    let clone = aarc.clone();

    // Empty means "no current value", so reads spin-out until reinit/set
    let err = clone.spinʳ::<i32> (10) .err().unwrap();
    assert_eq! (err, AArcErr::SpinOut);

    // Reinitialize through clone...
    let _ = clone.spin_set (7i32) .unwrap();
    // ...and observe from original: same shared control block.
    let guard = aarc.spin_read::<i32>().unwrap();
    assert_eq! (*guard, 7)}

  fn catch_unwind_silent<F: FnOnce() -> R + UnwindSafe, R> (f: F) -> thread::Result<R> {
    let prev_hook = panic::take_hook();
    panic::set_hook (Box::new (|_| {}));
    let res = panic::catch_unwind (f);
    panic::set_hook (prev_hook);
    res}

  #[test] fn test_evict_on_panic() {
    let aarc = AArc::none();
    let _ = aarc.spin_default::<i32>().unwrap();

    let res = catch_unwind_silent (|| {
      let _guard = aarc.spin_write::<i32>().unwrap();
      panic! ("test panic");});
    // Unwind: AWriteGuard::drop detects panicking()==true, evicts data (drops i32, sets EMPTY_BIT).

    assert! (res.is_err());

    // Unlike std::Mutex, no poisoning — just eviction. AArc is now empty, not broken.
    assert_eq! (aarc.status(), (0, "empty"));  // Write lock is cleared during panic unwind.
    let err = aarc.spinʳ::<i32> (10) .err().unwrap();
    assert_eq! (err, AArcErr::SpinOut);

    // Can be reinitialized normally after panic
    let guard = aarc.spin_default::<i32>().unwrap();
    assert_eq! (*guard, 0);}

  // A type whose drop panics. Dangerous: if this drop runs during unwind
  // (i.e., while already panicking), it triggers a double-panic → process abort.
  // catch_unwind_silent isolates each test so we only ever single-panic into
  // the catch, and InitGuard's cleanup finds None (data already .take()n).
  struct PanicOnDrop;
  impl Drop for PanicOnDrop {
    fn drop (&mut self) {
      panic! ("PanicOnDrop");}}

  #[test] fn test_write_bit_stuck_on_panic() {
    let aarc = AArc::none();
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

  #[test] fn test_evict_stuck_on_panic() {
    let aarc = AArc::none();
    let _ = aarc.spin_set (PanicOnDrop) .unwrap();

    let res = catch_unwind_silent (|| {
      // evictᵗ acquires WRITE_BIT, .take()s the value, then drop(old)
      // panics from PanicOnDrop. InitGuard unwinds: data already .take()n
      // so cleanup finds None (no second PanicOnDrop drop → no abort).
      let _ = aarc.evict();});

    assert! (res.is_err());

    // Same guarantee: WRITE_BIT cleared, AArc still usable
    let guard = aarc.spin_set (42i32) .unwrap();
    assert_eq! (*guard, 42);}

  #[bench] fn bench_spin_read (b: &mut test::Bencher) {
    let aarc = AArc::none();
    let _ = aarc.spin_default::<i32>().unwrap();
    b.iter (|| {
      let guard = aarc.spin_read::<i32>().unwrap();
      test::black_box (*guard);});}

  #[bench] fn bench_spin_write (b: &mut test::Bencher) {
    let aarc = AArc::none();
    let _ = aarc.spin_default::<i32>().unwrap();
    b.iter (|| {
      let mut guard = aarc.spin_write::<i32>().unwrap();
      *guard = test::black_box (*guard + 1);});}

  #[bench] fn bench_clone (b: &mut test::Bencher) {
    let aarc = AArc::none();
    let _ = aarc.spin_default::<i32>().unwrap();
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
    let aarc = AArc::none();
    let _ = aarc.spin_default::<i32>().unwrap();

    // spin_set can store closures that return Result
    let guard = aarc.spin_set::<BoxFnReI32> (Box::new (|| Ok (42))) .unwrap();
    assert_eq! (guard().unwrap(), 42);  // Callable through AWriteGuard.
    drop (guard);

    let read_guard = aarc.spin_read::<BoxFnReI32>().unwrap();
    assert_eq! (read_guard().unwrap(), 42);  // Callable through AReadGuard too (Fn).
    drop (read_guard);

    let mut counter = 0u32;
    let guard = aarc.spin_set::<BoxFnMutReU32> (Box::new (move || {
      counter += 1;
      Ok (counter)})) .unwrap();
    drop (guard);

    // FnMut: needs AWriteGuard for stateful calls
    let mut write_guard = aarc.spin_write::<BoxFnMutReU32>().unwrap();
    assert_eq! (write_guard().unwrap(), 1);
    assert_eq! (write_guard().unwrap(), 2);
    drop (write_guard);

    b.iter (|| {
      let mut guard = aarc.spin_write::<BoxFnMutReU32>().unwrap();
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
    let aarc = AArc::none();
    let _ = aarc.spin_default::<i32>().unwrap();

    let aarc_clone = aarc.clone();
    let handle = thread::spawn (move || {
      loop {
        // Spins until the value is u32 (type-aware spinning)
        let guard = aarc_clone.spin_write::<u32>().unwrap();
        if *guard == 999 {break;}
        test::black_box (*guard);
        guard.set::<i32> (0i32);}});  // Swap back to i32 for the other thread.

    b.iter (|| {
      // This thread writes i32 → u32, the other writes u32 → i32
      let guard = aarc.spin_write::<i32>().unwrap();
      test::black_box (guard.set::<u32> (42u32));});

    let guard = aarc.spin_write::<i32>().unwrap();
    guard.set::<u32> (999u32);  // Sentinel to stop the other thread.
    handle.join().unwrap();}

  #[test] fn test_inner_value_dropped_once() {
    struct DropCounter (Arc<AtomicUsize>);
    impl Drop for DropCounter {
      fn drop (&mut self) {
        self.0.fetch_add (1, Ordering::Relaxed);}}
    let counter = Arc::new (AtomicUsize::new (0));
    // Dropping the last AArc drops the control block, which drops the inner value.
    // count!=1 would mean double-free (unsound) or leak (resource bug).
    { let aarc = AArc::none();
      let _ = aarc.spin_set (DropCounter (counter.clone())) .unwrap();
    }  // AArc dropped: refcount 1→0, fence(Acquire), Box::from_raw frees ControlBlock + data.
    assert_eq! (counter.load (Ordering::Relaxed), 1);}

  #[test] fn test_benign_read_guard_drop() {
    let aarc = AArc::none();
    let _ = aarc.spin_default::<i32>().unwrap();
    // Multiple AReadGuards can coexist (shared read access)
    { let guard1 = aarc.spin_read::<i32>().unwrap();
      let guard2 = aarc.spin_read::<i32>().unwrap();
      assert_eq! (aarc.status(), (2, ""));  // Two active readers.
      assert_eq! (*guard1, 0);
      assert_eq! (*guard2, 0); }
    assert_eq! (aarc.status(), (0, ""));  // Both readers dropped.
    // If AReadGuard::drop failed to clear READ_INC, this would spin-out
    let mut write_guard = aarc.spin_write::<i32>().unwrap();
    assert_eq! (aarc.status(), (0, "write-locked"));  // One active writer.
    *write_guard = 42;
    assert_eq! (*write_guard, 42);}

  #[test] fn test_benign_write_guard_drop() {
    let aarc = AArc::none();
    let _ = aarc.spin_default::<i32>().unwrap();
    { let mut write_guard = aarc.spin_write::<i32>().unwrap();
      *write_guard = 99; }  // AWriteGuard dropped here, releases exclusive lock.
    // If AWriteGuard::drop failed to clear WRITE_BIT, this would spin-out
    let read_guard = aarc.spin_read::<i32>().unwrap();
    assert_eq! (*read_guard, 99);}

  #[test] fn test_benign_clone_drops() {
    let aarc = AArc::none();
    let _ = aarc.spin_set (String::from ("hello")) .unwrap();
    // Clones share the same control block whenever ptr is non-null (including evicted/EMPTY_BIT states)
    let clone1 = aarc.clone();
    let clone2 = aarc.clone();
    drop (clone1);  // Refcount 3→2; data untouched, only ref bookkeeping.
    { let guard = clone2.spin_read::<String>().unwrap();
      assert_eq! (*guard, "hello");}
    drop (aarc);  // Refcount 2→1; control block + String still alive for clone2.
    { let guard = clone2.spin_read::<String>().unwrap();
      assert_eq! (*guard, "hello");}}}  // clone2 dropped: refcount 1→0, String deallocated.

  #[test] fn test_upgrade() {
    let aarc = AArc::none();
    let _ = aarc.spin_default::<i32>().unwrap();
    let read_guard = aarc.spin_read::<i32>().unwrap();
    assert_eq! (*read_guard, 0);
    assert_eq! (aarc.status(), (1, ""));
    // upgrade converts AReadGuard to AWriteGuard without downcasting
    let mut write_guard = read_guard.upgrade().unwrap();
    assert_eq! (aarc.status(), (0, "write-locked"));
    *write_guard = 42;
    drop (write_guard);
    let read_guard2 = aarc.spin_read::<i32>().unwrap();
    assert_eq! (*read_guard2, 42);}

  #[test] fn test_upgrade_spin_out() {
    let aarc = AArc::none();
    let _ = aarc.spin_default::<i32>().unwrap();
    let read_guard1 = aarc.spin_read::<i32>().unwrap();
    let read_guard2 = aarc.spin_read::<i32>().unwrap();
    // upgradeᵗ fails if there are other active readers, returning the original AReadGuard
    let (recovered_guard, err) = read_guard1.upgradeᵗ (10) .err().unwrap();
    assert_eq! (err, AArcErr::SpinOut);
    assert_eq! (aarc.status(), (2, ""));
    assert_eq! (*recovered_guard, 0);
    drop (recovered_guard);
    drop (read_guard2);
    assert_eq! (aarc.status(), (0, ""));}
