//! ### Error Handling (`Re<T>`)
//! Methods that can fail (e.g., due to spin-out or empty state) return `Re<T>`.
//! `Re<T>` is a custom `Result`-like enum (`Re::Ok(T)` or `Re::Err(String)`).
//! It implements `Try`, allowing the use of the `?` operator, and provides methods like `unwrap()`,
//! `expect()`, and `err()`.
//!
//! ### `AArc` Methods
//! * `const fn none() -> Self`
//!   Creates empty, uninitialized `AArc`. Ideal for `static` declarations.
//! * `fn clone (&self) -> Self`
//!   Clones `AArc`, disconnected if empty.
//! * `fn cloneᵗ (&self, spins: u32) -> Re<Self>`
//!   Clones `AArc`, returning error if out of spins or if instance is empty.
//! * `fn evict (&self) -> Re<()>`
//!   Evicts stored value, resetting `AArc` to empty. Uses default spin limit.
//! * `fn evictᵗ (&self, spins: u32) -> Re<()>`
//!   Evicts stored value with custom spin limit.
//! * `fn spin_init<T> (&self, init: &mut dyn FnMut() -> Re<T>) -> Re<ReadGuard<'_, T>>`
//!   Initializes `AArc` if empty, returns read guard. Uses default spin limit. Spins if downcast fails.
//! * `fn spin_initᵗ<T> (&self, spins: u32, init: &mut dyn FnMut() -> Re<T>) -> Re<ReadGuard<'_, T>>`
//!   Initializes with custom spin limit. Spins if downcast fails.
//! * `fn spin_default<T> (&self) -> Re<ReadGuard<'_, T>>`
//!   Initializes with `T::default()` if empty. Uses default spin limit. Spins if downcast fails.
//! * `fn spin_defaultᵗ<T> (&self, spins: u32) -> Re<ReadGuard<'_, T>>`
//!   Initializes with `T::default()` with custom spin limit. Spins if downcast fails.
//! * `fn spin_read<T> (&self) -> Re<ReadGuard<'_, T>>`
//!   Acquires read lock and downcasts to `T`. Uses default spin limit. Spins if downcast fails.
//! * `fn spin_readᵗ<T> (&self, spins: u32) -> Re<ReadGuard<'_, T>>`
//!   Acquires read lock with custom spin limit. Spins if downcast fails.
//! * `fn spin_write<T> (&self) -> Re<WriteGuard<'_, T>>`
//!   Acquires exclusive write lock and downcasts to `T`. Uses default spin limit. Spins if downcast fails.
//! * `fn spin_writeᵗ<T> (&self, spins: u32) -> Re<WriteGuard<'_, T>>`
//!   Acquires write lock with custom spin limit. Spins if downcast fails.
//! * `fn spin_set<T> (&self, val: T) -> Re<WriteGuard<'_, T>>`
//!   Acquires write lock and sets new value of type `T`, returning typed guard. Uses default spin limit.
//! * `fn spin_setᵗ<T> (&self, spins: u32, val: T) -> Re<WriteGuard<'_, T>>`
//!   Acquires write lock and sets new value with custom spin limit.
//!
//! ### Guard Methods
//! * `WriteGuard::set<U> (self, val: U) -> WriteGuard<'_, U>`
//!   Replaces stored value with new type `U` and returns new typed guard.
//! * `WriteGuard::evict (self)`
//!   Evicts stored value while holding write lock.
//!
//! If a thread panics while holding a `WriteGuard`, the stored data is
//! evicted (`drop`ped) rather than poisoned. Other threads will see the `AArc` as empty.
//! `ReadGuard`s are safe to drop during a panic; they simply release the read lock.
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

pub struct AArc {
  ptr: std::sync::atomic::AtomicPtr<ControlBlock>}

struct ControlBlock {
  state: std::sync::atomic::AtomicU32,
  data: std::cell::UnsafeCell<Option<Box<dyn std::any::Any + Send + Sync>>>}

const REF_INC: u32 = 1;
const REF_MASK: u32 = 0x000F_FFFF;
const READ_INC: u32 = 0x0010_0000;
const READ_MASK: u32 = 0x3FF0_0000;
const WRITE_BIT: u32 = 0x4000_0000;
const EMPTY_BIT: u32 = 0x8000_0000;

unsafe impl Send for AArc {}
unsafe impl Sync for AArc {}

impl Clone for AArc {
  /// Clones the AArc. Disconnected if empty.
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

impl AArc {
  pub const fn none() -> Self {
    AArc {ptr: AtomicPtr::new (ptr::null_mut())}}
  
  /// Clones the AArc, returning an error if out of spins or if the instance is empty.
  pub fn cloneᵗ (&self, spins: u32) -> Re<Self> {
    for spin in 0..spins {
      let ptr = self.ptr.load (Ordering::Acquire);
      if !ptr.is_null() {
        let cb = unsafe {&*ptr};
        let state = cb.state.load (Ordering::Acquire);
        if state & EMPTY_BIT == 0 {
          if (state & REF_MASK) == REF_MASK {return Re::Err ("refcount overflow".into())}
          if cb.state.compare_exchange_weak (state, state + REF_INC, Ordering::AcqRel, Ordering::Relaxed) .is_ok() {
            return Re::Ok (AArc {ptr: AtomicPtr::new (ptr)})}
          continue}}
      if spin % 10 == 0 {spin_loop()} else {pause_yield()}}
    Re::Err ("spin-out or empty".into())}

  pub fn evictᵗ (&self, spins: u32) -> Re<()> {
    for spin in 0..spins {
      let ptr = self.ptr.load (Ordering::Acquire);
      if ptr.is_null() {return Re::Ok (())}
      let cb = unsafe {&*ptr};
      let state = cb.state.load (Ordering::Acquire);
      if state & WRITE_BIT == 0 && state & READ_MASK == 0 {
        if cb.state.compare_exchange_weak (state, state | WRITE_BIT, Ordering::AcqRel, Ordering::Relaxed) .is_ok() {
          let mut guard = InitGuard {cb: ptr, success: false, _marker: PhantomData};
          let old = unsafe {(*cb.data.get()).take()};
          drop (old);
          guard.success = true;
          let mut current = cb.state.load (Ordering::Relaxed);
          loop {
            let new = (current | EMPTY_BIT) & !WRITE_BIT;
            match cb.state.compare_exchange_weak (current, new, Ordering::Release, Ordering::Relaxed) {
              Ok (_) => return Re::Ok (()),
              Err (x) => current = x}}}
        continue}
      if spin % 10 == 0 {spin_loop()} else {pause_yield()}}
    Re::Err ("spin-out".into())}

  pub fn evict (&self) -> Re<()> {
    self.evictᵗ (unsafe {SPIN_OUT})}

  pub fn spin_initᵗ<T: Send + Sync + 'static> (&self, spins: u32, init: &mut dyn FnMut() -> Re<T>)
  -> Re<ReadGuard<'_, T>> {
    for spin in 0..spins {
      let ptr = self.ptr.load (Ordering::Acquire);
      if ptr.is_null() {
        let cb = Box::into_raw (Box::new (ControlBlock {
          state: AtomicU32::new (REF_INC | WRITE_BIT | EMPTY_BIT),
          data: UnsafeCell::new (None)}));
        match self.ptr.compare_exchange (ptr::null_mut(), cb, Ordering::AcqRel, Ordering::Acquire) {
          Ok (_) => return self.do_init (cb, init),
          Err (_) => {
            unsafe {let _ = Box::from_raw (cb);}
            continue}}
      } else {
        let cb = unsafe {&*ptr};
        let state = cb.state.load (Ordering::Acquire);
        if state & WRITE_BIT == 0 {
          if state & EMPTY_BIT != 0 {
            if cb.state.compare_exchange (state, state | WRITE_BIT, Ordering::AcqRel, Ordering::Relaxed) .is_ok() {
              return self.do_init (ptr, init)}}
          else {
            if (state & READ_MASK) == READ_MASK {return Re::Err ("reader overflow".into())}
            if cb.state.compare_exchange_weak (state, state + READ_INC, Ordering::AcqRel, Ordering::Relaxed) .is_ok() {
              let data_ref = unsafe {&*cb.data.get()};
              if let Some (any_box) = data_ref {
                if let Some (typed_ref) = any_box.downcast_ref::<T>() {
                  return Re::Ok (ReadGuard {cb, ptr: typed_ref as *const T, _phantom: PhantomData})}}
              cb.state.fetch_sub (READ_INC, Ordering::Release);}
            else {continue}}}}
      if spin % 10 == 0 {spin_loop()} else {pause_yield()}}
    Re::Err ("spin-out".into())}

  fn do_init<T: Send + Sync + 'static> (&self, cb_ptr: *mut ControlBlock, init: &mut dyn FnMut() -> Re<T>)
  -> Re<ReadGuard<'_, T>> {
    let mut guard = InitGuard {cb: cb_ptr, success: false, _marker: PhantomData};
    match init() {
      Re::Ok (val) => {
        let cb = unsafe {&*cb_ptr};
        let old = unsafe {(*cb.data.get()).take()};
        unsafe {*cb.data.get() = Some (Box::new (val))}
        drop (old);
        let ptr = unsafe {(&*cb.data.get()).as_ref().unwrap().downcast_ref::<T>().unwrap() as *const T};
        guard.success = true;

        let mut current = cb.state.load (Ordering::Relaxed);
        loop {
          let new = (current & !WRITE_BIT & !EMPTY_BIT) + READ_INC;
          match cb.state.compare_exchange_weak (current, new, Ordering::Release, Ordering::Relaxed) {
            Ok (_) => break, Err (x) => current = x}}
        Re::Ok (ReadGuard {cb, ptr, _phantom: PhantomData})}
      Re::Err (e) => Re::Err (e)}}

  pub fn spin_defaultᵗ<T: Default + Send + Sync + 'static> (&self, spins: u32) -> Re<ReadGuard<'_, T>> {
    self.spin_initᵗ (spins, &mut || Re::Ok (T::default()))}

  pub fn spin_init<T: Send + Sync + 'static> (&self, init: &mut dyn FnMut() -> Re<T>) -> Re<ReadGuard<'_, T>> {
    self.spin_initᵗ (unsafe {SPIN_OUT}, init)}

  pub fn spin_default<T: Default + Send + Sync + 'static> (&self) -> Re<ReadGuard<'_, T>> {
    self.spin_defaultᵗ (unsafe {SPIN_OUT})}

  pub fn spin_readᵗ<T: 'static> (&self, spins: u32) -> Re<ReadGuard<'_, T>> {
    for spin in 0..spins {
      let ptr = self.ptr.load (Ordering::Acquire);
      if !ptr.is_null() {
        let cb = unsafe {&*ptr};
        let state = cb.state.load (Ordering::Acquire);
        if state & WRITE_BIT == 0 && state & EMPTY_BIT == 0 {
          if (state & READ_MASK) == READ_MASK {return Re::Err ("reader overflow".into())}
          if cb.state.compare_exchange_weak (state, state + READ_INC, Ordering::AcqRel, Ordering::Relaxed) .is_ok() {
            let data_ref = unsafe {&*cb.data.get()};
            if let Some (any_box) = data_ref {
              if let Some (typed_ref) = any_box.downcast_ref::<T>() {
                return Re::Ok (ReadGuard {cb, ptr: typed_ref as *const T, _phantom: PhantomData})}}
            cb.state.fetch_sub (READ_INC, Ordering::Release);}
          else {continue}}}
      if spin % 10 == 0 {spin_loop()} else {pause_yield()}}
    Re::Err ("spin-out".into())}
  
  pub fn spin_read<T: 'static> (&self) -> Re<ReadGuard<'_, T>> {
    self.spin_readᵗ (unsafe {SPIN_OUT})}
  
  pub fn spin_writeᵗ<T: 'static> (&self, spins: u32) -> Re<WriteGuard<'_, T>> {
    for spin in 0..spins {
      let ptr = self.ptr.load (Ordering::Acquire);
      if !ptr.is_null() {
        let cb = unsafe {&*ptr};
        let state = cb.state.load (Ordering::Acquire);
        if state & WRITE_BIT == 0 && state & READ_MASK == 0 && state & EMPTY_BIT == 0 {
          if cb.state.compare_exchange_weak (state, state | WRITE_BIT, Ordering::AcqRel, Ordering::Relaxed).is_ok() {
            let data_mut = unsafe {&mut *cb.data.get()};
            if let Some (any_box) = data_mut {
              if let Some (typed_mut) = any_box.downcast_mut::<T>() {
                return Re::Ok (WriteGuard {cb, ptr: typed_mut as *mut T, _phantom: PhantomData})}}
            cb.state.fetch_and (!WRITE_BIT, Ordering::Release);}
          else {continue}}}
      if spin % 10 == 0 {spin_loop()} else {pause_yield()}}
    Re::Err ("spin-out".into())}
  
  pub fn spin_write<T: 'static> (&self) -> Re<WriteGuard<'_, T>> {
    self.spin_writeᵗ (unsafe {SPIN_OUT})}
  
  pub fn spin_setᵗ<T: Send + Sync + 'static> (&self, spins: u32, val: T) -> Re<WriteGuard<'_, T>> {
    for spin in 0..spins {
      let ptr = self.ptr.load (Ordering::Acquire);
      if ptr.is_null() {
        let cb = Box::into_raw (Box::new (ControlBlock {
          state: AtomicU32::new (REF_INC | WRITE_BIT | EMPTY_BIT),
          data: UnsafeCell::new (None)}));
        match self.ptr.compare_exchange (ptr::null_mut(), cb, Ordering::AcqRel, Ordering::Acquire) {
          Ok (_) => {
            // InitGuard ensures cleanup if any operation panics before we return the WriteGuard.
            let mut guard = InitGuard {cb, success: false, _marker: PhantomData};
            let cb = unsafe {&*cb};
            unsafe {*cb.data.get() = Some (Box::new (val))}
            let data_ptr = unsafe {(&mut *cb.data.get()).as_mut().unwrap().downcast_mut::<T>().unwrap() as *mut T};
            cb.state.fetch_and (!EMPTY_BIT, Ordering::Release);
            guard.success = true;
            return Re::Ok (WriteGuard {cb, ptr: data_ptr, _phantom: PhantomData})}
          Err (_) => {
            unsafe {let _ = Box::from_raw (cb);}
            continue}}
      } else {
        let cb = unsafe {&*ptr};
        let state = cb.state.load (Ordering::Acquire);
        if state & WRITE_BIT == 0 && state & READ_MASK == 0 {
          if cb.state.compare_exchange_weak (state, state | WRITE_BIT, Ordering::AcqRel, Ordering::Relaxed) .is_ok() {
            // Use InitGuard to ensure WRITE_BIT is cleared if `drop(old)` panics.
            // Without this, a panic during drop would leave the lock permanently stuck.
            let mut guard = InitGuard {cb: ptr, success: false, _marker: PhantomData};
            let old = unsafe {(*cb.data.get()).take()};
            unsafe {*cb.data.get() = Some (Box::new (val))}
            drop (old);
            let data_ptr = unsafe {(&mut *cb.data.get()).as_mut().unwrap().downcast_mut::<T>().unwrap() as *mut T};
            cb.state.fetch_and (!EMPTY_BIT, Ordering::Release);
            guard.success = true;
            return Re::Ok (WriteGuard {cb, ptr: data_ptr, _phantom: PhantomData})}
          continue}}
      if spin % 10 == 0 {spin_loop()} else {pause_yield()}}
    Re::Err ("spin-out".into())}

  pub fn spin_set<T: Send + Sync + 'static> (&self, val: T) -> Re<WriteGuard<'_, T>> {
    self.spin_setᵗ (unsafe {SPIN_OUT}, val)}}

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

pub struct ReadGuard<'a, T> {
  cb: *const ControlBlock,
  ptr: *const T,
  _phantom: PhantomData<&'a T>}

impl<'a, T: 'static> Deref for ReadGuard<'a, T> {
  type Target = T;
  fn deref (&self) -> &T {
    unsafe {&*self.ptr}}}

impl<'a, T> Drop for ReadGuard<'a, T> {
  fn drop (&mut self) {
    let cb = unsafe {&*self.cb};
    cb.state.fetch_sub (READ_INC, Ordering::Release);}}

pub struct WriteGuard<'a, T> {
  cb: *const ControlBlock,
  ptr: *mut T,
  _phantom: PhantomData<&'a mut T>}

impl<'a, T: 'static> Deref for WriteGuard<'a, T> {
  type Target = T;
  fn deref (&self) -> &T {
    unsafe {&*self.ptr}}}

impl<'a, T: 'static> DerefMut for WriteGuard<'a, T> {
  fn deref_mut (&mut self) -> &mut T {
    unsafe {&mut *self.ptr}}}

impl<'a, T> WriteGuard<'a, T> {
  pub fn set<U: Send + Sync + 'static> (self, val: U) -> WriteGuard<'a, U> {
    let cb = unsafe {&*self.cb};
    let old = unsafe {(*cb.data.get()).take()};
    unsafe {*cb.data.get() = Some (Box::new (val))}
    drop (old);
    let ptr = unsafe {(&mut *cb.data.get()).as_mut().unwrap().downcast_mut::<U>().unwrap() as *mut U};
    cb.state.fetch_and (!EMPTY_BIT, Ordering::Release);
    let guard = WriteGuard {cb: self.cb, ptr, _phantom: PhantomData};
    forget (self);
    guard}
  
  pub fn evict (self) {
    let cb = unsafe {&*self.cb};
    let old = unsafe {(*cb.data.get()).take()};
    drop (old);
    let mut current = cb.state.load (Ordering::Relaxed);
    loop {
      let new = (current | EMPTY_BIT) & !WRITE_BIT;
      match cb.state.compare_exchange_weak (current, new, Ordering::Release, Ordering::Relaxed) {
        Ok (_) => break, Err (x) => current = x}}
    forget (self)}}

impl<'a, T> Drop for WriteGuard<'a, T> {
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
  type BoxFnReI32 = Box<dyn Fn() -> Re<i32> + Send + Sync>;
  type BoxFnMutReU32 = Box<dyn FnMut() -> Re<u32> + Send + Sync>;

  #[test] fn test_basic_init_and_read() {
    let aarc = AArc::none();  // start empty
    // spin_default initializes with T::default() if empty, returns ReadGuard
    let guard = aarc.spin_default::<i32>().unwrap();
    assert_eq! (*guard, 0);  // ReadGuard derefs to &T.
    drop (guard);  // Must drop ReadGuard before spin_write; no reader→writer upgrade.

    // spin_write acquires exclusive write lock
    let write_guard = aarc.spin_write::<i32>().unwrap();
    // set drops the old value inside, then stores the new one (can even change type)
    let mut write_guard = write_guard.set (42i32);
    assert_eq! (*write_guard, 42);
    *write_guard = 43;  // DerefMut allows in-place mutation
    assert_eq! (*write_guard, 43);}  // WriteGuard dropped: clears WRITE_BIT, data persists.

  #[test] fn test_closure_storage() {
    let aarc = AArc::none();

    // spin_initᵗ with custom spin limit; closure-based init
    let _ = aarc.spin_initᵗ::<BoxFnI32> (100, &mut || {
      Re::Ok (Box::new (|| 77))}) .unwrap();

    // Fn closures callable through ReadGuard (Deref gives &self)
    let read_guard = aarc.spin_read::<BoxFnI32>().unwrap();
    assert_eq! (read_guard(), 77);
    drop (read_guard);

    // spin_setᵗ acquires write, drops old Box<dyn Fn> closure, stores new Box<dyn FnMut>.
    // If the old closure held resources, they'd be released here during the drop.
    let mut write_guard = aarc.spin_setᵗ::<BoxFnMutI32> (100, Box::new ({
      let mut counter = 0;
      move || {
        counter += 1;
        counter}})) .unwrap();

    // FnMut closures need WriteGuard (DerefMut gives &mut self)
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
    let _ = aarc.spin_initᵗ::<Box<dyn Animal>> (100, &mut || {
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
    let _ = aarc.spin_default::<i32>().unwrap();

    let guard = aarc.spin_read::<i32>().unwrap();
    assert_eq! (*guard, 0);
    drop (guard);

    aarc.evict().unwrap();  // Drops stored i32, sets EMPTY_BIT. AArc is now empty.

    // Reads spin-out on empty AArc
    let err = aarc.spin_readᵗ::<i32> (10) .err().unwrap();
    assert_eq! (err, "spin-out");

    // But can be reinitialized
    let guard = aarc.spin_default::<i32>().unwrap();
    assert_eq! (*guard, 0);}

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
    // Unwind: WriteGuard::drop detects panicking()==true, evicts data (drops i32, sets EMPTY_BIT).

    assert! (res.is_err());

    // Unlike std::Mutex, no poisoning — just eviction. AArc is now empty, not broken.
    let err = aarc.spin_readᵗ::<i32> (10) .err().unwrap();
    assert_eq! (err, "spin-out");

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
    let _ = aarc.spin_set (PanicOnDrop).unwrap();

    let res = catch_unwind_silent (|| {
      // spin_set acquires WRITE_BIT, .take()s old value, stores 42i32,
      // then drop(old) panics. InitGuard is live on the stack: during
      // unwind it clears WRITE_BIT|sets EMPTY_BIT. Data was already
      // .take()n, so InitGuard's drop finds None — no double-panic.
      let _ = aarc.spin_set (42i32);});

    assert! (res.is_err());

    // InitGuard cleared WRITE_BIT despite the panic, so AArc is usable
    let guard = aarc.spin_set (42i32).unwrap();
    assert_eq! (*guard, 42);}

  #[test] fn test_evict_stuck_on_panic() {
    let aarc = AArc::none();
    let _ = aarc.spin_set (PanicOnDrop).unwrap();

    let res = catch_unwind_silent (|| {
      // evictᵗ acquires WRITE_BIT, .take()s the value, then drop(old)
      // panics from PanicOnDrop. InitGuard unwinds: data already .take()n
      // so cleanup finds None (no second PanicOnDrop drop → no abort).
      let _ = aarc.evict();});

    assert! (res.is_err());

    // Same guarantee: WRITE_BIT cleared, AArc still usable
    let guard = aarc.spin_set (42i32).unwrap();
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

    // spin_set can store closures that return Re
    let guard = aarc.spin_set::<BoxFnReI32> (Box::new (|| Re::Ok (42))).unwrap();
    assert_eq! (guard().unwrap(), 42);  // Callable through WriteGuard.
    drop (guard);

    let read_guard = aarc.spin_read::<BoxFnReI32>().unwrap();
    assert_eq! (read_guard().unwrap(), 42);  // Callable through ReadGuard too (Fn).
    drop (read_guard);

    let mut counter = 0u32;
    let guard = aarc.spin_set::<BoxFnMutReU32> (Box::new (move || {
      counter += 1;
      Re::Ok (counter)})) .unwrap();
    drop (guard);

    // FnMut: needs WriteGuard for stateful calls
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
        Re::Ok (c)});
      // Alternates between spin_set (drop + create) and set (in-place swap)
      if is_odd {
        drop (guard);
        test::black_box (aarc.spin_set::<BoxFnMutReU32> (next).unwrap());}
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
    // Multiple ReadGuards can coexist (shared read access)
    { let guard1 = aarc.spin_read::<i32>().unwrap();
      let guard2 = aarc.spin_read::<i32>().unwrap();
      assert_eq! (*guard1, 0);
      assert_eq! (*guard2, 0); }
    // If ReadGuard::drop failed to clear READ_INC, this would spin-out
    let mut write_guard = aarc.spin_write::<i32>().unwrap();
    *write_guard = 42;
    assert_eq! (*write_guard, 42);}

  #[test] fn test_benign_write_guard_drop() {
    let aarc = AArc::none();
    let _ = aarc.spin_default::<i32>().unwrap();
    { let mut write_guard = aarc.spin_write::<i32>().unwrap();
      *write_guard = 99; }  // WriteGuard dropped here, releases exclusive lock.
    // If WriteGuard::drop failed to clear WRITE_BIT, this would spin-out
    let read_guard = aarc.spin_read::<i32>().unwrap();
    assert_eq! (*read_guard, 99);}

  #[test] fn test_benign_clone_drops() {
    let aarc = AArc::none();
    let _ = aarc.spin_set (String::from ("hello")) .unwrap();
    // Clones share the same control block
    let clone1 = aarc.clone();
    let clone2 = aarc.clone();
    drop (clone1);  // Refcount 3→2; data untouched, only ref bookkeeping.
    { let guard = clone2.spin_read::<String>().unwrap();
      assert_eq! (*guard, "hello");}
    drop (aarc);  // Refcount 2→1; control block + String still alive for clone2.
    { let guard = clone2.spin_read::<String>().unwrap();
      assert_eq! (*guard, "hello");}}}  // clone2 dropped: refcount 1→0, String deallocated.
