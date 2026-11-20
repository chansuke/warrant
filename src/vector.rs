//! Vectors for the IR runtime (M2-2): a shared buffer and a window into it.
//! `rest` and `slice` narrow the window without copying. `cons` and
//! `concat` write into the buffer in place when no other value refers to it
//! (`Rc::get_mut`), so a value never changes once another can see it.
//! Buffer slots outside every window are dead: in-place writes reuse them.

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

impl Vector {
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
    pub fn rest(mut self) -> Vector {
        if let Some(buf) = Rc::get_mut(&mut self.buf) {
            buf[self.start] = DEAD;
        }
        self.start += 1;
        self.len -= 1;
        self
    }

    /// The caller has checked `lo <= hi <= len`.
    pub fn slice(mut self, lo: usize, hi: usize) -> Vector {
        self.start += lo;
        self.len = hi - lo;
        self
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
        let room = self.len.max(1);
        let mut buf = Vec::with_capacity(room + 1 + self.len);
        buf.resize(room, DEAD);
        buf.push(x);
        buf.extend_from_slice(self.as_slice());
        let len = self.len + 1;
        (Vector { buf: Rc::new(buf), start: room, len }, Copied { alloc: true, elems: len })
    }

    pub fn concat(mut self, other: &Vector) -> (Vector, Copied) {
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
