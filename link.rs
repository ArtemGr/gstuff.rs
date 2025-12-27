use crate::fail;
use crate::re::Re;
use fomat_macros::fomat;
use indexmap::IndexMap as IndexMapB;
use inlinable_string::InlinableString;
use serde_json::Value as Json;
use std::any::Any;
use std::sync::{Mutex, MutexGuard};

type IndexMap<K, V> = IndexMapB<K, V, gxhash::GxBuildHasher>;
pub type Fun = fn (&str, u64, &mut dyn Any) -> Re<Json>;
pub type Map = IndexMap<InlinableString, Fun>;

static FUNS: Mutex<Option<Map>> = Mutex::new (None);

pub fn funs() -> Re<MutexGuard<'static, Option<Map>>> {
  let mut funs = FUNS.lock()?;
  if funs.is_none() {*funs = Some (IndexMap::default())}
  return Re::Ok (funs)}

pub fn c (fun: &str, s: &str, u: u64, a: &mut dyn Any) -> Re<Json> {
  let funs = FUNS.lock()?;
  let func: Option<&Fun> = match *funs {
    Some (ref funs) => funs.get (fun),
    None => fail! ("!funs")};
  let func: Option<&Fun> = unsafe {std::mem::transmute (func)};  // Shed lifetime as functions are global
  drop (funs);
  match func {
    Some (func) => func (s, u, a),
    None => fail! ("!c," (fun))}}

/// Like `c`, but uses nil arguments and returns ()
pub fn c0 (fun: &str) -> Re<()> {
  c (fun, "", 0, &mut 0)?; Re::Ok(())}
