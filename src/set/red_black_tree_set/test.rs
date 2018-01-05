/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use super::*;

mod iter {
    use super::*;

    #[test]
    fn test_iter_empty() -> () {
        let set: RedBlackTreeSet<i32> = RedBlackTreeSet::new();

        for _ in set.iter() {
            panic!("iterator should be empty");
        }
    }

    #[test]
    fn test_iter() -> () {
        let mut set = RedBlackTreeSet::new();
        let limit: usize = 100;

        for i in 0..limit {
            set = set.insert(i);
        }

        let mut touched = vec![false; limit];

        for v in set.iter() {
            assert!(!touched[*v]);
            touched[*v] = true;
        }

        assert!(touched.iter().all(|b| *b));
    }

    #[test]
    fn test_iter_size_hint() -> () {
        let set = RedBlackTreeSet::new()
            .insert(0)
            .insert(1)
            .insert(2);
        let mut iterator = set.iter();

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
        let set = RedBlackTreeSet::new()
            .insert(0)
            .insert(1)
            .insert(2);
        let mut left = 3;

        for _ in &set {
            left -= 1;
            assert!(left >= 0);
        }

        assert_eq!(left, 0);
    }
}

mod compile_time {
    use super::*;

    #[test]
    fn test_is_send() -> () {
        let _: Box<Send> = Box::new(RedBlackTreeSet::<i32>::new());
    }

    #[test]
    fn test_is_sync() -> () {
        let _: Box<Sync> = Box::new(RedBlackTreeSet::<i32>::new());
    }
}

#[test]
fn test_insert() -> () {
    let mut set = RedBlackTreeSet::new();
    assert_eq!(set.size(), 0);

    set = set.insert("foo");
    assert_eq!(set.size(), 1);
    assert!(set.contains("foo"));

    set = set.insert("bar");
    assert_eq!(set.size(), 2);
    assert!(set.contains("foo"));
    assert!(set.contains("bar"));

    set = set.insert("baz");
    assert_eq!(set.size(), 3);
    assert!(set.contains("foo"));
    assert!(set.contains("bar"));
    assert!(set.contains("baz"));

    set = set.insert("foo");
    assert_eq!(set.size(), 3);
    assert!(set.contains("foo"));
    assert!(set.contains("bar"));
    assert!(set.contains("baz"));
}

#[test]
fn test_first() -> () {
    let set = RedBlackTreeSet::new()
        .insert(3)
        .insert(2)
        .insert(1);

    assert_eq!(set.first(), Some(&1));
}

#[test]
fn test_last() -> () {
    let set = RedBlackTreeSet::new()
        .insert(3)
        .insert(2)
        .insert(1);

    assert_eq!(set.last(), Some(&3));
}

#[test]
fn test_remove() -> () {
    let mut set = RedBlackTreeSet::new()
        .insert("foo")
        .insert("bar")
        .insert("mumble")
        .insert("baz");
    let empty_set: RedBlackTreeSet<i32> = RedBlackTreeSet::new();

    assert_eq!(empty_set.remove(&3), empty_set);

    assert_eq!(set.size(), 4);

    set = set.remove("not-there");
    assert_eq!(set.size(), 4);

    assert!(set.contains("foo"));
    assert!(set.contains("bar"));
    assert!(set.contains("mumble"));
    assert!(set.contains("baz"));

    set = set.remove("mumble");
    assert_eq!(set.size(), 3);

    assert!(set.contains("foo"));
    assert!(set.contains("bar"));
    assert!(!set.contains("mumble"));
    assert!(set.contains("baz"));

    set = set.remove("foo");
    assert_eq!(set.size(), 2);

    assert!(!set.contains("foo"));

    set = set.remove("baz");
    assert_eq!(set.size(), 1);

    assert!(!set.contains("baz"));

    set = set.remove("bar");
    assert_eq!(set.size(), 0);

    assert!(!set.contains("bar"));
}

#[test]
fn test_from_iterator() -> () {
    let vec: Vec<&str> = vec![("two"), ("five")];
    let set: RedBlackTreeSet<&str> = vec.iter().map(|v| *v).collect();
    let expected_set =
        RedBlackTreeSet::new()
            .insert("two")
            .insert("five");

    assert_eq!(set, expected_set);
}

#[test]
fn test_default() -> () {
    let set: RedBlackTreeSet<u32> = RedBlackTreeSet::default();

    assert_eq!(set.size(), 0);
    assert!(set.is_empty());
}

#[test]
fn test_display() -> () {
    let empty_set: RedBlackTreeSet<i32> = RedBlackTreeSet::new();
    let singleton_set = RedBlackTreeSet::new()
        .insert("hi");
    let set = RedBlackTreeSet::new()
        .insert(5)
        .insert(12);

    assert_eq!(format!("{}", empty_set), "{}");
    assert_eq!(format!("{}", singleton_set), "{hi}");
    assert!(format!("{}", set) == "{5, 12}" || format!("{}", set) == "{12, 5}");
}

#[test]
fn test_eq() -> () {
    let set_1 = RedBlackTreeSet::new()
        .insert("a")
        .insert("b");
    let set_1_prime = RedBlackTreeSet::new()
        .insert("a")
        .insert("b");
    let set_1_prime_2 = RedBlackTreeSet::new()
        .insert("a")
        .insert("b")
        .insert("b");
    let set_2 = RedBlackTreeSet::new()
        .insert("a")
        .insert("b")
        .insert("c");

    assert_eq!(set_1, set_1_prime);
    assert_eq!(set_1, set_1_prime_2);
    assert_eq!(set_1, set_1);
    assert_eq!(set_2, set_2);

    // We also check this since `assert_ne!()` does not call `ne`.
    assert!(set_1.ne(&set_2));
}

#[test]
fn test_clone() -> () {
    let set =
        RedBlackTreeSet::new()
            .insert("hello")
            .insert("there");
    let clone = set.clone();

    assert_eq!(clone.size(), set.size());
    assert!(clone.contains("hello"));
    assert!(clone.contains("there"));
}

#[cfg(feature = "serde")]
#[test]
fn test_serde() {
    use bincode::{serialize, deserialize, Bounded};
    let rbtreeset: RedBlackTreeSet<i32> = RedBlackTreeSet::from_iter(vec![5,6,7,8].into_iter());
    let encoded = serialize(&rbtreeset, Bounded(100)).unwrap();
    let decoded: RedBlackTreeSet<i32> = deserialize(&encoded).unwrap();
    assert_eq!(rbtreeset, decoded);
}
