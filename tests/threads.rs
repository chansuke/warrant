//! Runtime values shared between threads (M2-4).

use std::sync::{Arc, Barrier};
use warrant::rt::Value;
use warrant::vector::Vector;

/// Two chains `a_k = [a_(k-1)]` and `b_k = [a_(k-1)]` share every level, and
/// two threads with small stacks drop one chain each at the same time.
/// Whichever owner lets go of a level last frees it, and must do so with
/// the work list rather than by recursing into the level below.
///
/// A stress test: the race it guards against (one owner fails `get_mut`,
/// the other lets go, then the first drops last) has a window of a few
/// instructions, and this test did not hit it with the old code either.
/// The guarantee comes from `Arc::into_inner`.
#[test]
fn owners_on_two_threads_free_a_shared_chain_without_recursion() {
    const LEVELS: usize = 300_000;
    for _ in 0..5 {
        let mut a = Value::Vec(Vector::new(Vec::new()));
        let mut b = Value::Vec(Vector::new(Vec::new()));
        for _ in 0..LEVELS {
            b = Value::Vec(Vector::new(vec![a.clone()]));
            a = Value::Vec(Vector::new(vec![a]));
        }
        let go = Arc::new(Barrier::new(2));
        let threads: Vec<_> = [a, b]
            .into_iter()
            .map(|v| {
                let go = go.clone();
                std::thread::Builder::new()
                    .stack_size(64 << 10)
                    .spawn(move || {
                        go.wait();
                        drop(v);
                    })
                    .unwrap()
            })
            .collect();
        for t in threads {
            t.join().unwrap();
        }
    }
}
