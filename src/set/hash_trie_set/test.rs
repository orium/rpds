/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use super::*;
use alloc::vec::Vec;
use pretty_assertions::assert_eq;
use static_assertions::assert_impl_all;

assert_impl_all!(HashTrieSetSync<i32>: Send, Sync);

#[allow(dead_code)]
fn compile_time_macro_hash_trie_set_sync_is_send_and_sync() -> impl Send + Sync {
    ht_set_sync!(0)
}

mod iter {
    use super::*;
    use pretty_assertions::assert_eq;

    #[allow(clippy::never_loop)]
    #[test]
    fn test_iter_empty() {
        let set: HashTrieSet<i32> = HashTrieSet::new();

        for _ in set.iter() {
            panic!("iterator should be empty");
        }
    }

    #[test]
    fn test_iter() {
        let mut set = HashTrieSet::new();
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
        let set = ht_set![0, 1, 2];
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
    fn test_into_iterator() {
        let set = ht_set![0, 1, 2];
        let mut left = 3;

        for _ in &set {
            left -= 1;
            assert!(left >= 0);
        }

        assert_eq!(left, 0);
    }
}

#[test]
fn test_macro_ht_set() {
    let set_1 = HashTrieSet::new().insert(1);
    let set_1_2_3 = HashTrieSet::new().insert(1).insert(2).insert(3);

    assert_eq!(HashTrieSet::<u32>::new(), ht_set![]);
    assert_eq!(set_1, ht_set![1]);
    assert_eq!(set_1_2_3, ht_set![1, 2, 3]);
}

#[test]
fn test_insert() {
    let mut set = HashTrieSet::new();
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
    let mut set = HashTrieSet::new();
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
fn test_remove() {
    let mut set = ht_set!["foo", "bar", "mumble", "baz"];
    let empty_set: HashTrieSet<i32> = HashTrieSet::new();

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
    let mut set = ht_set!["foo", "bar", "mumble", "baz"];

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
fn test_get() {
    let mut set = HashTrieSet::new();

    set = set.insert("foo");
    assert_eq!(set.get("foo"), Some(&"foo"));

    set = set.insert("bar");
    assert_eq!(set.get("foo"), Some(&"foo"));
    assert_eq!(set.get("bar"), Some(&"bar"));
}

#[test]
fn test_is_disjoint() {
    assert!(!HashTrieSet::is_disjoint(&ht_set![1, 2, 3], &ht_set![1, 2, 3]));
    assert!(!HashTrieSet::is_disjoint(&ht_set![1, 2, 3], &ht_set![0, 1]));
    assert!(HashTrieSet::is_disjoint(&ht_set![1, 2, 3, 7, 16], &ht_set![0, 4, 17]));
}

#[test]
fn test_is_subset() {
    let set = ht_set![1, 2, 3];

    assert!(set.is_subset(&set));

    assert!(HashTrieSet::is_subset(&ht_set![], &ht_set![1, 2, 3]));
    assert!(HashTrieSet::is_subset(&ht_set![1, 2, 3], &ht_set![1, 2, 3]));
    assert!(!HashTrieSet::is_subset(&ht_set![1, 2, 3], &ht_set![1, 2, 5, 6]));
    assert!(HashTrieSet::is_subset(&ht_set![1, 2, 3], &ht_set![1, 2, 3, 5, 6]));
    assert!(!HashTrieSet::is_subset(&ht_set![1, 2, 3, 5, 6], &ht_set![1, 2, 3]));
}

#[test]
fn test_is_superset() {
    let set = ht_set![1, 2, 3];

    assert!(set.is_superset(&set));

    assert!(HashTrieSet::is_superset(&ht_set![1, 2, 3], &ht_set![]));
    assert!(HashTrieSet::is_superset(&ht_set![1, 2, 3], &ht_set![1, 2, 3]));
    assert!(!HashTrieSet::is_superset(&ht_set![1, 2, 5, 6], &ht_set![1, 2, 3]));
    assert!(HashTrieSet::is_superset(&ht_set![1, 2, 3, 5, 6], &ht_set![1, 2, 3]));
    assert!(!HashTrieSet::is_superset(&ht_set![1, 2, 3], &ht_set![1, 2, 3, 5, 6]));
}

#[test]
fn test_from_iterator() {
    let vec: Vec<&str> = vec![("two"), ("five")];
    let set: HashTrieSet<&str> = vec.iter().copied().collect();
    let expected_set = ht_set!["two", "five"];

    assert_eq!(set, expected_set);
}

#[test]
fn test_default() {
    let set: HashTrieSet<u32> = HashTrieSet::default();

    assert_eq!(set.size(), 0);
    assert!(set.is_empty());
}

#[test]
fn test_display() {
    let empty_set: HashTrieSet<i32> = HashTrieSet::new();
    let singleton_set = ht_set!["hi"];
    let set = ht_set![5, 12];

    assert_eq!(format!("{}", empty_set), "{}");
    assert_eq!(format!("{}", singleton_set), "{hi}");
    assert!(format!("{set}") == "{5, 12}" || format!("{set}") == "{12, 5}");
}

#[test]
fn test_eq() {
    let set_1 = ht_set!["a", "b"];
    let set_1_prime = ht_set!["a", "b"];
    let set_1_prime_2 = ht_set!["a", "b", "b"];
    let set_2 = ht_set!["a", "b", "c"];

    assert_eq!(set_1, set_1_prime);
    assert_eq!(set_1, set_1_prime_2);
    assert_eq!(set_1, set_1);
    assert_eq!(set_2, set_2);

    // We also check this since `assert_ne!()` does not call `ne`.
    assert!(set_1.ne(&set_2));
}

#[test]
fn test_eq_pointer_kind_consistent() {
    let set_a = ht_set!["a"];
    let set_a_sync = ht_set_sync!["a"];
    let set_b = ht_set!["b"];
    let set_b_sync = ht_set_sync!["b"];

    assert!(set_a == set_a_sync);
    assert!(set_a != set_b_sync);
    assert!(set_b == set_b_sync);
}

#[test]
fn test_clone() {
    let set = ht_set!["hello", "there"];
    let clone = set.clone();

    assert_eq!(clone.size(), set.size());
    assert!(clone.contains("hello"));
    assert!(clone.contains("there"));
}

#[cfg(feature = "serde")]
#[test]
fn test_serde() {
    let set: HashTrieSet<i32> = ht_set![5, 6, 7, 8];
    let encoded = serde_json::to_string(&set).unwrap();
    let decoded: HashTrieSet<i32> = serde_json::from_str(&encoded).unwrap();

    assert_eq!(set, decoded);
}
