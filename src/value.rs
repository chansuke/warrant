//! Values of the IR runtime, and its vectors (M2-2): a shared buffer and a
//! window into it.
//! `rest` and `slice` narrow the window without copying. `cons` and
//! `concat` write into the buffer in place when no other value refers to it
//! (`Arc::get_mut`), so a value never changes once another can see it.
//! Buffer slots outside every window are dead: in-place writes reuse them.
//! A window that shrinks below a quarter of its buffer is copied out, so a
//! small slice does not keep a large buffer alive.

use crate::builtin::Builtin;
use crate::ir::Lambda;
use std::mem::ManuallyDrop;
use std::sync::Arc;

#[derive(Clone)]
pub enum Value {
    Int(i64),
    Bool(bool),
    Str(Arc<str>),
    Vec(Vector),
    Closure(Arc<Closure>),
    Func(usize),
    Builtin(Builtin),
}

pub struct Closure {
    pub(crate) code: Arc<Lambda>,
    pub(crate) captured: Vec<Value>,
}

impl Drop for Closure {
    fn drop(&mut self) {
        free_nested(&mut self.captured);
    }
}

/// Drops `values` with a work list instead of recursion when they own
/// vectors or closures, so freeing a deeply nested value (a vector of a
/// vector of ..., or the buffers a ConsTail loop releases at once) never
/// overflows the stack. Values another reference still holds are left alone.
/// `Arc::into_inner` hands the contents to exactly one of the owners that
/// let go, so this holds when owners on several threads drop at once.
fn free_nested(values: &mut Vec<Value>) {
    if !values.iter().any(|v| matches!(v, Value::Vec(_) | Value::Closure(_))) {
        return;
    }
    let mut work = std::mem::take(values);
    while let Some(v) = work.pop() {
        match v {
            Value::Vec(xs) => {
                if let Some(mut elems) = xs.take_buf() {
                    work.append(&mut elems);
                }
            }
            Value::Closure(c) => {
                if let Some(mut c) = Arc::into_inner(c) {
                    work.append(&mut c.captured);
                }
            }
            _ => {}
        }
        // Whatever is dropped here has nothing left inside it.
    }
}

/// Fills dead buffer slots.
const DEAD: Value = Value::Bool(false);

#[derive(Clone)]
pub struct Vector {
    /// Released only through `Arc::into_inner` (`take_buf`), so of the
    /// owners that drop it, exactly one gets the elements, even when they
    /// drop at once on different threads.
    buf: ManuallyDrop<Arc<Vec<Value>>>,
    start: usize,
    len: usize,
}

/// What an operation copied, for the profiler's `vec-allocs` / `vec-elems`.
pub struct Copied {
    /// Whether a new buffer was allocated.
    pub alloc: bool,
    pub elems: usize,
}

impl Copied {
    const NOTHING: Copied = Copied { alloc: false, elems: 0 };
}

impl Drop for Vector {
    fn drop(&mut self) {
        // SAFETY: `buf` is not used again; `drop` runs once.
        let buf = unsafe { ManuallyDrop::take(&mut self.buf) };
        if let Some(mut elems) = Arc::into_inner(buf) {
            free_nested(&mut elems);
        }
    }
}

impl Vector {
    /// Gives up this reference to the buffer without running `drop`, and
    /// returns the elements if it was the last one.
    pub(crate) fn take_buf(self) -> Option<Vec<Value>> {
        let mut me = ManuallyDrop::new(self);
        // SAFETY: `me` is never dropped, so `buf` is taken exactly once.
        Arc::into_inner(unsafe { ManuallyDrop::take(&mut me.buf) })
    }

    pub fn new(items: Vec<Value>) -> Vector {
        let len = items.len();
        Vector { buf: ManuallyDrop::new(Arc::new(items)), start: 0, len }
    }

    pub fn as_slice(&self) -> &[Value] {
        &self.buf[self.start..self.start + self.len]
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// The caller has checked that `self` is not empty.
    pub fn rest(mut self) -> (Vector, Copied) {
        if let Some(buf) = Arc::get_mut(&mut self.buf) {
            buf[self.start] = DEAD;
        }
        self.start += 1;
        self.len -= 1;
        self.compacted()
    }

    /// The caller has checked `lo <= hi <= len`.
    pub fn slice(mut self, lo: usize, hi: usize) -> (Vector, Copied) {
        self.start += lo;
        self.len = hi - lo;
        self.compacted()
    }

    /// Copies the window out once it covers under a quarter of the buffer.
    /// Each copy at least quarters the buffer, so the copies a run of
    /// narrowings makes add up to less than the original buffer.
    fn compacted(self) -> (Vector, Copied) {
        if self.len * 4 >= self.buf.len() {
            return (self, Copied::NOTHING);
        }
        let v = Vector::new(self.as_slice().to_vec());
        (v, Copied { alloc: true, elems: self.len })
    }

    pub fn cons(mut self, x: Value) -> (Vector, Copied) {
        if self.start > 0 {
            if let Some(buf) = Arc::get_mut(&mut self.buf) {
                self.start -= 1;
                buf[self.start] = x;
                self.len += 1;
                return (self, Copied::NOTHING);
            }
        }
        // Room in front for as many more conses as there are elements, so a
        // run of conses copies O(1) elements each on average.
        let mut v = self.with_room(self.len.max(1));
        let copied = Copied { alloc: true, elems: v.len + 1 };
        let buf = Arc::get_mut(&mut v.buf).expect("just copied");
        v.start -= 1;
        buf[v.start] = x;
        v.len += 1;
        (v, copied)
    }

    /// A copy of the window in a new buffer with `room` dead slots in front.
    fn with_room(&self, room: usize) -> Vector {
        let mut buf = Vec::with_capacity(room + self.len);
        buf.resize(room, DEAD);
        buf.extend_from_slice(self.as_slice());
        Vector { buf: ManuallyDrop::new(Arc::new(buf)), start: room, len: self.len }
    }

    pub fn concat(mut self, mut other: Vector) -> (Vector, Copied) {
        // Write the shorter side into a buffer nothing else refers to:
        // `(concat acc [x])` appends to `acc`, `(concat [x] acc)` prepends.
        if self.len < other.len && Arc::get_mut(&mut other.buf).is_some() {
            let mut copied = Copied { alloc: false, elems: self.len };
            if other.start < self.len {
                other = other.with_room(self.len + other.len);
                copied = Copied { alloc: true, elems: self.len + other.len };
            }
            let buf = Arc::get_mut(&mut other.buf).expect("unique, or just copied");
            other.start -= self.len;
            buf[other.start..other.start + self.len].clone_from_slice(self.as_slice());
            other.len += self.len;
            return (other, copied);
        }
        if let Some(buf) = Arc::get_mut(&mut self.buf) {
            buf.truncate(self.start + self.len);
            buf.extend_from_slice(other.as_slice());
            self.len += other.len;
            return (self, Copied { alloc: false, elems: other.len });
        }
        let mut buf = Vec::with_capacity(self.len + other.len);
        buf.extend_from_slice(self.as_slice());
        buf.extend_from_slice(other.as_slice());
        let len = buf.len();
        (Vector::new(buf), Copied { alloc: true, elems: len })
    }
}
