/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use super::*;

mod iter {
    use super::*;

    #[test]
    fn test_iter_empty() {
        let set: RedBlackTreeSet<i32> = RedBlackTreeSet::new();

        for _ in set.iter() {
            panic!("iterator should be empty");
        }
    }

    #[test]
    fn test_iter() {
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
    fn test_iter_size_hint() {
        let set = rbt_set![0, 1, 2];
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
    fn test_iter_sorted() {
        let set = rbt_set![5, 6, 2, 1];
        let mut iterator = set.iter();

        assert_eq!(iterator.next(), Some(&1));
        assert_eq!(iterator.next(), Some(&2));
        assert_eq!(iterator.next(), Some(&5));
        assert_eq!(iterator.next(), Some(&6));
        assert_eq!(iterator.next(), None);
    }

    #[test]
    fn test_into_iterator() {
        let set = rbt_set![0, 1, 2];
        let mut left = 3;

        for _ in &set {
            left -= 1;
            assert!(left >= 0);
        }

        assert_eq!(left, 0);
    }

    #[test]
    fn test_range_iterator() {
        let set = rbt_set![-20, -12, -8, 0, 2, -10, -7, -3, 5, 8, 10, 13, 17, 20];
        let mut iterator = set.range(-7..=13);

        assert_eq!(iterator.next(), Some(&-7));
        assert_eq!(iterator.next(), Some(&-3));
        assert_eq!(iterator.next_back(), Some(&13));
        assert_eq!(iterator.next_back(), Some(&10));
        assert_eq!(iterator.next_back(), Some(&8));
        assert_eq!(iterator.next(), Some(&0));
        assert_eq!(iterator.next(), Some(&2));
        assert_eq!(iterator.next(), Some(&5));
        assert_eq!(iterator.next_back(), None);
        assert_eq!(iterator.next(), None);
    }
}

mod compile_time {
    use super::*;

    #[test]
    fn test_is_send() {
        let _: Box<Send> = Box::new(RedBlackTreeSet::<i32>::new());
    }

    #[test]
    fn test_is_sync() {
        let _: Box<Sync> = Box::new(RedBlackTreeSet::<i32>::new());
    }
}

#[test]
fn test_macro_rbt_set() {
    let set_1 = RedBlackTreeSet::new().insert(1);
    let set_1_2_3 = RedBlackTreeSet::new().insert(1).insert(2).insert(3);

    assert_eq!(RedBlackTreeSet::<u32>::new(), rbt_set![]);
    assert_eq!(set_1, rbt_set![1]);
    assert_eq!(set_1_2_3, rbt_set![1, 2, 3]);
}

#[test]
fn test_insert() {
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
fn test_insert_mut() {
    let mut set = RedBlackTreeSet::new();
    assert_eq!(set.size(), 0);

    set.insert_mut("foo");
    assert_eq!(set.size(), 1);
    assert!(set.contains("foo"));

    set.insert_mut("bar");
    assert_eq!(set.size(), 2);
    assert!(set.contains("foo"));
    assert!(set.contains("bar"));

    set.insert_mut("baz");
    assert_eq!(set.size(), 3);
    assert!(set.contains("foo"));
    assert!(set.contains("bar"));
    assert!(set.contains("baz"));

    set.insert_mut("foo");
    assert_eq!(set.size(), 3);
    assert!(set.contains("foo"));
    assert!(set.contains("bar"));
    assert!(set.contains("baz"));
}

#[test]
fn test_first() {
    let set = rbt_set![3, 2, 1];

    assert_eq!(set.first(), Some(&1));
}

#[test]
fn test_last() {
    let set = rbt_set![3, 2, 1];

    assert_eq!(set.last(), Some(&3));
}

#[test]
fn test_remove() {
    let mut set = rbt_set!["foo", "bar", "mumble", "baz"];
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
fn test_remove_mut() {
    let mut set = rbt_set!["foo", "bar", "mumble", "baz"];

    assert_eq!(set.size(), 4);

    assert!(!set.remove_mut("not-there"));
    assert_eq!(set.size(), 4);

    assert!(set.contains("foo"));
    assert!(set.contains("bar"));
    assert!(set.contains("mumble"));
    assert!(set.contains("baz"));

    assert!(set.remove_mut("mumble"));
    assert_eq!(set.size(), 3);

    assert!(set.contains("foo"));
    assert!(set.contains("bar"));
    assert!(!set.contains("mumble"));
    assert!(set.contains("baz"));

    assert!(set.remove_mut("foo"));
    assert_eq!(set.size(), 2);

    assert!(!set.contains("foo"));

    assert!(set.remove_mut("baz"));
    assert_eq!(set.size(), 1);

    assert!(!set.contains("baz"));

    assert!(set.remove_mut("bar"));
    assert_eq!(set.size(), 0);

    assert!(!set.contains("bar"));
}

#[test]
fn test_is_disjoint() {
    assert!(!RedBlackTreeSet::is_disjoint(
        &rbt_set![1, 2, 3],
        &rbt_set![1, 2, 3]
    ));
    assert!(!RedBlackTreeSet::is_disjoint(
        &rbt_set![1, 2, 3],
        &rbt_set![0, 1]
    ));
    assert!(RedBlackTreeSet::is_disjoint(
        &rbt_set![1, 2, 3, 7, 16],
        &rbt_set![0, 4, 17]
    ));
}

#[test]
fn test_is_subset() {
    assert!(RedBlackTreeSet::is_subset(&rbt_set![], &rbt_set![1, 2, 3]));
    assert!(RedBlackTreeSet::is_subset(
        &rbt_set![1, 2, 3],
        &rbt_set![1, 2, 3]
    ));
    assert!(!RedBlackTreeSet::is_subset(
        &rbt_set![1, 2, 3],
        &rbt_set![1, 2, 5, 6]
    ));
    assert!(RedBlackTreeSet::is_subset(
        &rbt_set![1, 2, 3],
        &rbt_set![1, 2, 3, 5, 6]
    ));
    assert!(!RedBlackTreeSet::is_subset(
        &rbt_set![1, 2, 3, 5, 6],
        &rbt_set![1, 2, 3]
    ));
}

#[test]
fn test_is_superset() {
    assert!(RedBlackTreeSet::is_superset(
        &rbt_set![1, 2, 3],
        &rbt_set![]
    ));
    assert!(RedBlackTreeSet::is_superset(
        &rbt_set![1, 2, 3],
        &rbt_set![1, 2, 3]
    ));
    assert!(!RedBlackTreeSet::is_superset(
        &rbt_set![1, 2, 5, 6],
        &rbt_set![1, 2, 3]
    ));
    assert!(RedBlackTreeSet::is_superset(
        &rbt_set![1, 2, 3, 5, 6],
        &rbt_set![1, 2, 3]
    ));
    assert!(!RedBlackTreeSet::is_superset(
        &rbt_set![1, 2, 3],
        &rbt_set![1, 2, 3, 5, 6]
    ));
}

#[test]
fn test_from_iterator() {
    let vec: Vec<&str> = vec![("two"), ("five")];
    let set: RedBlackTreeSet<&str> = vec.iter().map(|v| *v).collect();
    let expected_set = rbt_set!["two", "five"];

    assert_eq!(set, expected_set);
}

#[test]
fn test_default() {
    let set: RedBlackTreeSet<u32> = RedBlackTreeSet::default();

    assert_eq!(set.size(), 0);
    assert!(set.is_empty());
}

#[test]
fn test_display() {
    let empty_set: RedBlackTreeSet<i32> = RedBlackTreeSet::new();
    let singleton_set = rbt_set!["hi"];
    let set = rbt_set![5, 12];

    assert_eq!(format!("{}", empty_set), "{}");
    assert_eq!(format!("{}", singleton_set), "{hi}");
    assert_eq!(format!("{}", set), "{5, 12}");
}

#[test]
fn test_eq() {
    let set_1 = rbt_set!["a", "b"];
    let set_1_prime = rbt_set!["a", "b"];
    let set_1_prime_2 = rbt_set!["a", "b", "b"];
    let set_2 = rbt_set!["a", "b", "c"];

    assert_eq!(set_1, set_1_prime);
    assert_eq!(set_1, set_1_prime_2);
    assert_eq!(set_1, set_1);
    assert_eq!(set_2, set_2);

    // We also check this since `assert_ne!()` does not call `ne`.
    assert!(set_1.ne(&set_2));
}

#[test]
fn test_clone() {
    let set = rbt_set!["hello", "there"];
    let clone = set.clone();

    assert_eq!(clone.size(), set.size());
    assert!(clone.contains("hello"));
    assert!(clone.contains("there"));
}

#[cfg(feature = "serde")]
#[test]
fn test_serde() {
    use bincode::{deserialize, serialize};
    let set: RedBlackTreeSet<i32> = rbt_set![5, 6, 7, 8];
    let encoded = serialize(&set).unwrap();
    let decoded: RedBlackTreeSet<i32> = deserialize(&encoded).unwrap();

    assert_eq!(set, decoded);
}
