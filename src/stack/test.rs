/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use super::*;
use alloc::vec::Vec;
use pretty_assertions::assert_eq;
use static_assertions::assert_impl_all;

assert_impl_all!(StackSync<i32>: Send, Sync);

#[allow(dead_code)]
fn compile_time_macro_stack_sync_is_send_and_sync() -> impl Send + Sync {
    stack_sync!(0)
}

mod iter {
    #[test]
    fn test_iter() {
        let stack = stack![2, 1, 0];
        let mut iterator = stack.iter();

        assert_eq!(iterator.next(), Some(&0));
        assert_eq!(iterator.next(), Some(&1));
        assert_eq!(iterator.next(), Some(&2));
        assert_eq!(iterator.next(), None);
    }

    #[test]
    fn test_iter_size_hint() {
        let stack = stack![2, 1, 0];
        let mut iterator = stack.iter();

        assert_eq!(iterator.size_hint(), (3, Some(3)));

        iterator.next();

        assert_eq!(iterator.size_hint(), (2, Some(2)));

        iterator.next();

        assert_eq!(iterator.size_hint(), (1, Some(1)));

        iterator.next();

        assert_eq!(iterator.size_hint(), (0, Some(0)));
    }

    #[test]
    fn test_into_iterator() {
        let stack = stack![3, 2, 1, 0];
        let mut left = 4;

        for (expected, n) in stack.into_iter().enumerate() {
            left -= 1;

            assert!(left >= 0);
            assert_eq!(*n, expected);
        }

        assert_eq!(left, 0);
    }
}

#[test]
fn test_new() {
    let empty_stack: Stack<i32> = Stack::new();

    assert!(empty_stack.list.is_empty());

    assert_eq!(empty_stack.size(), 0);
    assert!(empty_stack.is_empty());
}

#[test]
fn test_macro_stack() {
    let mut stack_1 = Stack::new();
    stack_1.push_mut(1);

    let mut stack_1_2_3 = Stack::new();

    stack_1_2_3.push_mut(1);
    stack_1_2_3.push_mut(2);
    stack_1_2_3.push_mut(3);

    assert_eq!(Stack::<u32>::new(), stack![]);
    assert_eq!(stack_1, stack![1]);
    assert_eq!(stack_1_2_3, stack![1, 2, 3]);
}

#[test]
fn test_peek() {
    let empty_stack: Stack<i32> = Stack::new();
    let singleton_stack = stack!["hello"];
    let stack = stack![3, 2, 1, 0];

    assert_eq!(empty_stack.peek(), None);
    assert_eq!(singleton_stack.peek(), Some(&"hello"));
    assert_eq!(stack.peek(), Some(&0));
}

#[test]
fn test_pop_mut() {
    let mut empty_stack: Stack<i32> = Stack::new();
    let mut singleton_stack = stack!["hello"];
    let mut stack = stack![3, 2, 1, 0];

    empty_stack.pop_mut();
    assert!(empty_stack.is_empty());

    singleton_stack.pop_mut();
    assert_eq!(singleton_stack.peek(), None);

    stack.pop_mut();
    assert_eq!(stack.peek(), Some(&1));
    assert_eq!(stack.size(), 3);
}

#[test]
fn test_pop() {
    let empty_stack: Stack<i32> = Stack::new();
    let singleton_stack = Stack::new().push("hello");
    let stack = Stack::new().push(3).push(2).push(1).push(0);

    assert!(empty_stack.pop().is_none());
    assert_eq!(singleton_stack.pop().unwrap().peek(), None);
    assert_eq!(stack.pop().unwrap().peek(), Some(&1));

    assert_eq!(stack.size(), 4);
    assert_eq!(stack.pop().unwrap().size(), 3);
}

#[test]
fn test_from_iterator() {
    let vec: Vec<u32> = vec![10, 11, 12, 13];
    let stack: Stack<u32> = vec.iter().copied().collect();

    assert!(vec.iter().eq(stack.iter()));
}

#[test]
fn test_default() {
    let stack: Stack<i32> = Stack::default();

    assert_eq!(stack.peek(), None);
    assert!(stack.is_empty());
}

#[test]
fn test_display() {
    let empty_stack: Stack<i32> = Stack::new();
    let singleton_stack = stack!["hello"];
    let stack = stack![3, 2, 1, 0];

    assert_eq!(format!("{}", empty_stack), "Stack()");
    assert_eq!(format!("{}", singleton_stack), "Stack(hello)");
    assert_eq!(format!("{}", stack), "Stack(0, 1, 2, 3)");
}

#[test]
fn test_eq() {
    let stack_1 = stack!["a", "a"];
    let stack_1_prime = stack!["a", "a"];
    let stack_2 = stack!["b", "a"];

    assert_ne!(stack_1, stack_2);
    assert_eq!(stack_1, stack_1);
    assert_eq!(stack_1, stack_1_prime);
    assert_eq!(stack_2, stack_2);
}

#[test]
fn test_eq_pointer_kind_consistent() {
    let stack_a = stack!["a"];
    let stack_a_sync = stack_sync!["a"];
    let stack_b = stack!["b"];
    let stack_b_sync = stack_sync!["b"];

    assert!(stack_a == stack_a_sync);
    assert!(stack_a != stack_b_sync);
    assert!(stack_b == stack_b_sync);
}

#[test]
fn test_partial_ord() {
    let stack_1 = stack!["a"];
    let stack_1_prime = stack!["a"];
    let stack_2 = stack!["b"];
    let stack_3 = stack![0.0];
    let stack_4 = stack![f32::NAN];

    assert_eq!(stack_1.partial_cmp(&stack_1_prime), Some(Ordering::Equal));
    assert_eq!(stack_1.partial_cmp(&stack_2), Some(Ordering::Less));
    assert_eq!(stack_2.partial_cmp(&stack_1), Some(Ordering::Greater));
    assert_eq!(stack_3.partial_cmp(&stack_4), None);
}

#[test]
fn test_ord() {
    let stack_1 = stack!["a"];
    let stack_1_prime = stack!["a"];
    let stack_2 = stack!["b"];

    assert_eq!(stack_1.cmp(&stack_1_prime), Ordering::Equal);
    assert_eq!(stack_1.cmp(&stack_2), Ordering::Less);
    assert_eq!(stack_2.cmp(&stack_1), Ordering::Greater);
}

#[test]
fn test_ord_pointer_kind_consistent() {
    let stack_a = stack!["a"];
    let stack_a_sync = stack_sync!["a"];
    let stack_b = stack!["b"];
    let stack_b_sync = stack_sync!["b"];

    assert!(stack_a <= stack_a_sync);
    assert!(stack_a < stack_b_sync);
    assert!(stack_b >= stack_b_sync);

    assert!(stack_a_sync >= stack_a);
    assert!(stack_b_sync > stack_a);
    assert!(stack_b_sync <= stack_b);
}

fn hash<T: Hash, P: SharedPointerKind>(stack: &Stack<T, P>) -> u64 {
    #[allow(deprecated)]
    let mut hasher = core::hash::SipHasher::new();

    stack.hash(&mut hasher);

    hasher.finish()
}

#[test]
fn test_hash() {
    let stack_1 = stack!["a"];
    let stack_1_prime = stack!["a"];
    let stack_2 = stack!["b", "a"];

    assert_eq!(hash(&stack_1), hash(&stack_1));
    assert_eq!(hash(&stack_1), hash(&stack_1_prime));
    assert_ne!(hash(&stack_1), hash(&stack_2));
}

#[test]
fn test_hash_pointer_kind_consistent() {
    let stack = stack!["a"];
    let stack_sync = stack_sync!["a"];

    assert_eq!(hash(&stack), hash(&stack_sync));
}

#[test]
fn test_clone() {
    let stack = stack!["there", "hello"];
    let clone = stack.clone();

    assert!(clone.iter().eq(stack.iter()));
    assert_eq!(clone.size(), stack.size());
}

#[cfg(feature = "serde")]
#[test]
fn test_serde() {
    let stack: Stack<i32> = stack![5, 6, 7, 8];
    let encoded = serde_json::to_string(&stack).unwrap();
    let decoded: Stack<i32> = serde_json::from_str(&encoded).unwrap();

    assert_eq!(stack, decoded);
}
