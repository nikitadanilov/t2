use bf_tree::{BfTree, LeafReadResult};
use libc::{EINVAL, ENAMETOOLONG, EEXIST, ENOENT};
use std::collections::BTreeMap;
use std::ffi::CStr;
use std::os::raw::{c_char, c_int, c_void};
use std::slice;
use std::sync::RwLock;

struct Db {
    tree: BfTree,
    mirror: RwLock<BTreeMap<Vec<u8>, Vec<u8>>>,
}

struct Iter {
    db: *mut Db,
    rows: Vec<(Vec<u8>, Vec<u8>)>,
    pos: usize,
    valid: bool,
}

fn as_slice<'a>(ptr: *const c_void, len: i32) -> Result<&'a [u8], c_int> {
    if ptr.is_null() || len < 0 {
        return Err(-EINVAL);
    }
    Ok(unsafe { slice::from_raw_parts(ptr as *const u8, len as usize) })
}

#[no_mangle]
pub extern "C" fn bftree_bn_db_open(path: *const c_char, _create_if_missing: bool, out_db: *mut *mut c_void) -> c_int {
    if path.is_null() || out_db.is_null() {
        return -EINVAL;
    }
    let cstr = unsafe { CStr::from_ptr(path) };
    let path = match cstr.to_str() {
        Ok(s) => s,
        Err(_) => return -EINVAL,
    };
    let tree = match BfTree::new(path, 64 * 1024 * 1024) {
        Ok(t) => t,
        Err(_) => return -EINVAL,
    };
    let db = Box::new(Db {
        tree,
        mirror: RwLock::new(BTreeMap::new()),
    });
    unsafe {
        *out_db = Box::into_raw(db) as *mut c_void;
    }
    0
}

#[no_mangle]
pub extern "C" fn bftree_bn_db_close(db: *mut c_void) {
    if !db.is_null() {
        unsafe {
            let _ = Box::from_raw(db as *mut Db);
        }
    }
}

#[no_mangle]
pub extern "C" fn bftree_bn_get(db: *mut c_void, key: *const c_void, ksize: i32, val: *mut c_void, vsize: *mut i32) -> c_int {
    if db.is_null() || val.is_null() || vsize.is_null() {
        return -EINVAL;
    }
    let key = match as_slice(key, ksize) {
        Ok(k) => k,
        Err(e) => return e,
    };
    let out_cap = unsafe { *vsize };
    if out_cap < 0 {
        return -EINVAL;
    }
    let out = unsafe { slice::from_raw_parts_mut(val as *mut u8, out_cap as usize) };
    let db = unsafe { &*(db as *mut Db) };
    match db.tree.read(key, out) {
        LeafReadResult::Found(n) => {
            unsafe { *vsize = n as i32 };
            0
        }
        LeafReadResult::Deleted => -ENOENT,
        LeafReadResult::NotFound => -ENOENT,
        _ => -ENAMETOOLONG,
    }
}

#[no_mangle]
pub extern "C" fn bftree_bn_put(db: *mut c_void, key: *const c_void, ksize: i32, val: *const c_void, vsize: i32) -> c_int {
    if db.is_null() {
        return -EINVAL;
    }
    let key = match as_slice(key, ksize) {
        Ok(k) => k,
        Err(e) => return e,
    };
    let val = match as_slice(val, vsize) {
        Ok(v) => v,
        Err(e) => return e,
    };
    let db = unsafe { &*(db as *mut Db) };
    db.tree.insert(key, val);
    db.mirror.write().expect("poisoned").insert(key.to_vec(), val.to_vec());
    0
}

#[no_mangle]
pub extern "C" fn bftree_bn_del(db: *mut c_void, key: *const c_void, ksize: i32) -> c_int {
    if db.is_null() {
        return -EINVAL;
    }
    let key = match as_slice(key, ksize) {
        Ok(k) => k,
        Err(e) => return e,
    };
    let db = unsafe { &*(db as *mut Db) };
    db.tree.delete(key);
    match db.mirror.write().expect("poisoned").remove(key) {
        Some(_) => 0,
        None => -ENOENT,
    }
}

#[no_mangle]
pub extern "C" fn bftree_bn_iter_new(_db: *mut c_void, out_it: *mut *mut c_void) -> c_int {
    if _db.is_null() || out_it.is_null() {
        return -EINVAL;
    }
    let it = Box::new(Iter {
        db: _db as *mut Db,
        rows: Vec::new(),
        pos: 0,
        valid: false,
    });
    unsafe {
        *out_it = Box::into_raw(it) as *mut c_void;
    }
    0
}

#[no_mangle]
pub extern "C" fn bftree_bn_iter_del(it: *mut c_void) {
    if !it.is_null() {
        unsafe {
            let _ = Box::from_raw(it as *mut Iter);
        }
    }
}

#[no_mangle]
pub extern "C" fn bftree_bn_iter_seek(it: *mut c_void, key: *const c_void, ksize: i32) -> c_int {
    if it.is_null() {
        return -EINVAL;
    }
    let key = match as_slice(key, ksize) {
        Ok(k) => k,
        Err(e) => return e,
    };
    let it = unsafe { &mut *(it as *mut Iter) };
    it.rows.clear();
    it.pos = 0;
    it.valid = false;
    if it.db.is_null() {
        return -EINVAL;
    }
    let db = unsafe { &*it.db };
    let mirror = db.mirror.read().expect("poisoned");
    for (k, v) in mirror.range(key.to_vec()..) {
        it.rows.push((k.clone(), v.clone()));
    }
    if it.rows.is_empty() {
        return -ENOENT;
    }
    it.valid = true;
    0
}

fn current(it: &Iter) -> Option<&(Vec<u8>, Vec<u8>)> {
    if it.valid && it.pos < it.rows.len() {
        Some(&it.rows[it.pos])
    } else {
        None
    }
}

#[no_mangle]
pub extern "C" fn bftree_bn_iter_next(it: *mut c_void) -> c_int {
    if it.is_null() {
        return -EINVAL;
    }
    let it = unsafe { &mut *(it as *mut Iter) };
    if !it.valid {
        return -ENOENT;
    }
    if it.pos + 1 >= it.rows.len() {
        it.valid = false;
        return -ENOENT;
    }
    it.pos += 1;
    0
}

#[no_mangle]
pub extern "C" fn bftree_bn_iter_prev(it: *mut c_void) -> c_int {
    if it.is_null() {
        return -EINVAL;
    }
    let it = unsafe { &mut *(it as *mut Iter) };
    if !it.valid || it.pos == 0 {
        it.valid = false;
        return -ENOENT;
    }
    it.pos -= 1;
    0
}

#[no_mangle]
pub extern "C" fn bftree_bn_iter_key(it: *mut c_void, key: *mut *const c_void, ksize: *mut i32) -> c_int {
    if it.is_null() || key.is_null() || ksize.is_null() {
        return -EINVAL;
    }
    let it = unsafe { &mut *(it as *mut Iter) };
    match current(it) {
        Some((k, _)) => {
            unsafe {
                *key = k.as_ptr() as *const c_void;
                *ksize = k.len() as i32;
            }
            0
        }
        None => -ENOENT,
    }
}

#[no_mangle]
pub extern "C" fn bftree_bn_iter_val(it: *mut c_void, val: *mut *const c_void, vsize: *mut i32) -> c_int {
    if it.is_null() || val.is_null() || vsize.is_null() {
        return -EINVAL;
    }
    let it = unsafe { &mut *(it as *mut Iter) };
    match current(it) {
        Some((_, v)) => {
            unsafe {
                *val = v.as_ptr() as *const c_void;
                *vsize = v.len() as i32;
            }
            0
        }
        None => -ENOENT,
    }
}

#[allow(dead_code)]
fn _errno_examples() -> c_int {
    -EEXIST
}
