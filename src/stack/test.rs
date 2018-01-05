/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use super::*;

mod iter {
    use super::*;

    #[test]
    fn test_iter() -> () {
        let stack = Stack::new()
            .push(2)
            .push(1)
            .push(0);
        let mut iterator = stack.iter();

        assert_eq!(iterator.next(), Some(&0));
        assert_eq!(iterator.next(), Some(&1));
        assert_eq!(iterator.next(), Some(&2));
        assert_eq!(iterator.next(), None);
    }

    #[test]
    fn test_iter_size_hint() -> () {
        let stack = Stack::new()
            .push(2)
            .push(1)
            .push(0);
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
    fn test_into_iterator() -> () {
        let stack = Stack::new()
            .push(3)
            .push(2)
            .push(1)
            .push(0);
        let mut expected = 0;
        let mut left = 4;

        for n in &stack {
            left -= 1;

            assert!(left >= 0);
            assert_eq!(*n, expected);

            expected += 1;
        }

        assert_eq!(left, 0);
    }
}

mod compile_time {
    use super::*;

    #[test]
    fn test_is_send() -> () {
        let _: Box<Send> = Box::new(Stack::<i32>::new());
    }

    #[test]
    fn test_is_sync() -> () {
        let _: Box<Sync> = Box::new(Stack::<i32>::new());
    }
}

#[test]
fn test_new() -> () {
    let empty_stack: Stack<i32> = Stack::new();

    assert!(empty_stack.list.is_empty());

    assert_eq!(empty_stack.size(), 0);
    assert!(empty_stack.is_empty());
}

#[test]
fn test_peek() -> () {
    let empty_stack: Stack<i32> = Stack::new();
    let singleton_stack = Stack::new()
        .push("hello");
    let stack = Stack::new()
        .push(3)
        .push(2)
        .push(1)
        .push(0);

    assert_eq!(empty_stack.peek(), None);
    assert_eq!(singleton_stack.peek(), Some(&"hello"));
    assert_eq!(stack.peek(), Some(&0));
}

#[test]
fn test_pop() -> () {
    let empty_stack: Stack<i32> = Stack::new();
    let singleton_stack = Stack::new()
        .push("hello");
    let stack = Stack::new()
        .push(3)
        .push(2)
        .push(1)
        .push(0);

    assert!(empty_stack.pop().is_none());
    assert_eq!(singleton_stack.pop().unwrap().peek(), None);
    assert_eq!(stack.pop().unwrap().peek(), Some(&1));

    assert_eq!(stack.size(), 4);
    assert_eq!(stack.pop().unwrap().size(), 3);
}

#[test]
fn test_from_iterator() -> () {
    let vec: Vec<u32> = vec![10, 11, 12, 13];
    let stack: Stack<u32> = vec.iter().map(|v| *v).collect();

    assert!(vec.iter().eq(stack.iter()));
}

#[test]
fn test_default() -> () {
    let stack: Stack<i32> = Stack::default();

    assert_eq!(stack.peek(), None);
    assert!(stack.is_empty());
}

#[test]
fn test_display() -> () {
    let empty_stack: Stack<i32> = Stack::new();
    let singleton_stack = Stack::new()
        .push("hello");
    let stack = Stack::new()
        .push(3)
        .push(2)
        .push(1)
        .push(0);

    assert_eq!(format!("{}", empty_stack), "Stack()");
    assert_eq!(format!("{}", singleton_stack), "Stack(hello)");
    assert_eq!(format!("{}", stack), "Stack(0, 1, 2, 3)");
}

#[test]
fn test_eq() -> () {
    let stack_1 = Stack::new()
        .push("a")
        .push("a");
    let stack_1_prime = Stack::new()
        .push("a")
        .push("a");
    let stack_2 = Stack::new()
        .push("b")
        .push("a");

    assert_ne!(stack_1, stack_2);
    assert_eq!(stack_1, stack_1);
    assert_eq!(stack_1, stack_1_prime);
    assert_eq!(stack_2, stack_2);
}

#[test]
fn test_partial_ord() -> () {
    let stack_1 = Stack::new()
        .push("a");
    let stack_1_prime = Stack::new()
        .push("a");
    let stack_2 = Stack::new()
        .push("b");
    let stack_3 = Stack::new()
        .push(0.0);
    let stack_4 = Stack::new()
        .push(::std::f32::NAN);

    assert_eq!(stack_1.partial_cmp(&stack_1_prime), Some(Ordering::Equal));
    assert_eq!(stack_1.partial_cmp(&stack_2), Some(Ordering::Less));
    assert_eq!(stack_2.partial_cmp(&stack_1), Some(Ordering::Greater));
    assert_eq!(stack_3.partial_cmp(&stack_4), None);
}

#[test]
fn test_ord() -> () {
    let stack_1 = Stack::new()
        .push("a");
    let stack_1_prime = Stack::new()
        .push("a");
    let stack_2 = Stack::new()
        .push("b");

    assert_eq!(stack_1.cmp(&stack_1_prime), Ordering::Equal);
    assert_eq!(stack_1.cmp(&stack_2), Ordering::Less);
    assert_eq!(stack_2.cmp(&stack_1), Ordering::Greater);
}

fn hash<T: Hash>(stack: &Stack<T>) -> u64 {
    let mut hasher = ::std::collections::hash_map::DefaultHasher::new();

    stack.hash(&mut hasher);

    hasher.finish()
}

#[test]
fn test_hash() -> () {
    let stack_1 = Stack::new()
        .push("a");
    let stack_1_prime = Stack::new()
        .push("a");
    let stack_2 = Stack::new()
        .push("b")
        .push("a");

    assert_eq!(hash(&stack_1), hash(&stack_1));
    assert_eq!(hash(&stack_1), hash(&stack_1_prime));
    assert_ne!(hash(&stack_1), hash(&stack_2));
}

#[test]
fn test_clone() -> () {
    let stack = Stack::new()
        .push("there")
        .push("hello");
    let clone = stack.clone();

    assert!(clone.iter().eq(stack.iter()));
    assert_eq!(clone.size(), stack.size());
}

#[cfg(feature = "serde")]
#[test]
fn test_serde() {
    use bincode::{serialize, deserialize, Bounded};
    let stack: Stack<i32> = Stack::from_iter(vec![5,6,7,8].into_iter());
    let encoded = serialize(&stack, Bounded(100)).unwrap();
    let decoded: Stack<i32> = deserialize(&encoded).unwrap();
    assert_eq!(stack, decoded);
}
