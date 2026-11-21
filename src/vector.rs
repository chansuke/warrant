//! Vectors for the IR runtime (M2-2): a shared buffer and a window into it.
//! `rest` and `slice` narrow the window without copying. `cons` and
//! `concat` write into the buffer in place when no other value refers to it
//! (`Rc::get_mut`), so a value never changes once another can see it.
//! Buffer slots outside every window are dead: in-place writes reuse them.
//! A window that shrinks below a quarter of its buffer is copied out, so a
//! small slice does not keep a large buffer alive.

use crate::rt::Value;
use std::rc::Rc;

/// Fills dead buffer slots.
const DEAD: Value = Value::Bool(false);

#[derive(Clone)]
pub struct Vector {
    buf: Rc<Vec<Value>>,
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
        if let Some(buf) = Rc::get_mut(&mut self.buf) {
            crate::rt::free_nested(buf);
        }
    }
}

impl Vector {
    /// The buffer, when no other value refers to it.
    pub(crate) fn unique_buf(&mut self) -> Option<&mut Vec<Value>> {
        Rc::get_mut(&mut self.buf)
    }

    pub fn new(items: Vec<Value>) -> Vector {
        let len = items.len();
        Vector { buf: Rc::new(items), start: 0, len }
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
        if let Some(buf) = Rc::get_mut(&mut self.buf) {
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
            if let Some(buf) = Rc::get_mut(&mut self.buf) {
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
        let buf = Rc::get_mut(&mut v.buf).expect("just copied");
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
        Vector { buf: Rc::new(buf), start: room, len: self.len }
    }

    pub fn concat(mut self, mut other: Vector) -> (Vector, Copied) {
        // Write the shorter side into a buffer nothing else refers to:
        // `(concat acc [x])` appends to `acc`, `(concat [x] acc)` prepends.
        if self.len < other.len && Rc::get_mut(&mut other.buf).is_some() {
            let mut copied = Copied { alloc: false, elems: self.len };
            if other.start < self.len {
                other = other.with_room(self.len + other.len);
                copied = Copied { alloc: true, elems: self.len + other.len };
            }
            let buf = Rc::get_mut(&mut other.buf).expect("unique, or just copied");
            other.start -= self.len;
            buf[other.start..other.start + self.len].clone_from_slice(self.as_slice());
            other.len += self.len;
            return (other, copied);
        }
        if let Some(buf) = Rc::get_mut(&mut self.buf) {
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
