/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use super::*;
use pretty_assertions::assert_eq;
use static_assertions::assert_impl_all;

assert_impl_all!(ListSync<i32>: Send, Sync);

#[allow(dead_code)]
fn compile_time_macro_list_sync_is_send_and_sync() -> impl Send + Sync {
    list_sync!(0)
}

mod iter {
    use super::*;
    use pretty_assertions::assert_eq;

    #[allow(clippy::explicit_iter_loop)]
    #[test]
    fn test_iter() {
        let limit = 1024;
        let mut list = List::new();
        let mut left = limit;

        for i in 0..limit {
            list.push_front_mut(i);
        }

        for v in list.iter() {
            left -= 1;
            assert_eq!(*v, left);
        }

        assert_eq!(left, 0);
    }

    #[test]
    fn test_iter_size_hint() {
        let list = list![0, 1, 2];
        let mut iterator = list.iter();

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
        let list = list![0, 1, 2, 3];
        let mut left = 4;

        for (expected, n) in list.into_iter().enumerate() {
            left -= 1;

            assert!(left >= 0);
            assert_eq!(*n, expected);
        }

        assert_eq!(left, 0);
    }
}

#[test]
fn test_new() {
    let empty_list: List<i32> = List::new();

    assert!(empty_list.head.is_none());

    assert_eq!(empty_list.len(), 0);
    assert!(empty_list.is_empty());
}

#[test]
fn test_macro_list() {
    let mut list_1 = List::new();

    list_1.push_front_mut(1);

    let mut list_1_2_3 = List::new();

    list_1_2_3.push_front_mut(3);
    list_1_2_3.push_front_mut(2);
    list_1_2_3.push_front_mut(1);

    assert_eq!(List::<u32>::new(), list![]);
    assert_eq!(list_1, list![1]);
    assert_eq!(list_1_2_3, list![1, 2, 3]);
}

#[test]
fn test_first() {
    let empty_list: List<i32> = List::new();
    let singleton_list = list!["hello"];
    let list = list![0, 1, 2, 3];

    assert_eq!(empty_list.first(), None);
    assert_eq!(singleton_list.first(), Some(&"hello"));
    assert_eq!(list.first(), Some(&0));
}

#[test]
fn test_first_mut() {
    let a = list![0, 1, 2, 3];
    let mut b = a.clone();
    *b.first_mut().unwrap() = -1;

    assert_eq!(a.first(), Some(&0));
    assert_eq!(b.first(), Some(&-1));
    assert!(a.iter().eq([0, 1, 2, 3].iter()));
    assert!(b.iter().eq([-1, 1, 2, 3].iter()));
}

#[test]
fn test_last() {
    let empty_list: List<i32> = List::new();
    let mut singleton_list = list!["hello"];
    let list = list![0, 1, 2, 3];

    assert_eq!(empty_list.last(), None);
    assert_eq!(singleton_list.last(), Some(&"hello"));
    assert_eq!(list.last(), Some(&3));

    singleton_list.drop_first_mut();
    assert_eq!(singleton_list.last(), None);
}

#[test]
fn test_drop_first() {
    let empty_list: List<i32> = List::new();
    let singleton_list = List::new().push_front("hello");
    let list = List::new().push_front(3).push_front(2).push_front(1).push_front(0);

    assert!(empty_list.is_empty());
    assert_eq!(singleton_list.drop_first().unwrap().first(), None);
    assert_eq!(list.drop_first().unwrap().first(), Some(&1));

    assert_eq!(list.len(), 4);
    assert_eq!(list.drop_first().unwrap().len(), 3);
}

#[test]
fn test_drop_first_mut() {
    let mut empty_list: List<i32> = List::new();
    let mut singleton_list = list!["hello"];
    let mut list = list![0, 1, 2, 3];

    empty_list.drop_first_mut();
    assert!(empty_list.is_empty());

    singleton_list.drop_first_mut();
    assert_eq!(singleton_list.first(), None);

    list.drop_first_mut();
    assert_eq!(list.first(), Some(&1));

    assert_eq!(list.len(), 3);
}

#[test]
fn test_reverse() {
    let empty_list: List<i32> = List::new();
    let singleton_list = List::new().push_front("hello");
    let list = List::new().push_front(3).push_front(2).push_front(1).push_front(0);
    let list_reversed = List::new().push_front(0).push_front(1).push_front(2).push_front(3);

    assert_eq!(empty_list.reverse(), empty_list);
    assert_eq!(empty_list.reverse().last(), None);
    assert_eq!(singleton_list.reverse(), singleton_list);
    assert_eq!(singleton_list.reverse().last(), Some(&"hello"));
    assert_eq!(list.reverse(), list_reversed);
    assert_eq!(list.reverse().last(), Some(&0));
}

#[test]
fn test_reverse_mut() {
    let mut empty_list: List<i32> = List::new();
    let mut singleton_list = list!["hello"];
    let mut list = list![0, 1, 2, 3];

    list.reverse_mut();
    singleton_list.reverse_mut();
    empty_list.reverse_mut();

    assert_eq!(empty_list, empty_list);
    assert_eq!(empty_list.last(), None);
    assert_eq!(singleton_list, singleton_list);
    assert_eq!(singleton_list.last(), Some(&"hello"));
    assert_eq!(list.last(), Some(&0));
}

#[test]
fn test_from_iterator() {
    let vec: Vec<u32> = vec![10, 11, 12, 13];
    let list: List<u32> = vec.iter().copied().collect();

    assert!(vec.iter().eq(list.iter()));
}

#[test]
fn test_default() {
    let list: List<i32> = List::default();

    assert_eq!(list.first(), None);
    assert_eq!(list.len(), 0);
}

#[test]
fn test_display() {
    let empty_list: List<i32> = List::new();
    let singleton_list = list!["hello"];
    let list = list![0, 1, 2, 3];

    assert_eq!(format!("{}", empty_list), "[]");
    assert_eq!(format!("{}", singleton_list), "[hello]");
    assert_eq!(format!("{}", list), "[0, 1, 2, 3]");
}

#[test]
fn test_eq() {
    let list_1 = list!["a", "a"];
    let list_1_prime = list!["a", "a"];
    let list_2 = list!["a", "b"];

    assert_ne!(list_1, list_2);
    assert_eq!(list_1, list_1);
    assert_eq!(list_1, list_1_prime);
    assert_eq!(list_2, list_2);
}

#[test]
fn test_eq_pointer_kind_consistent() {
    let list_a = list!["a"];
    let list_a_sync = list_sync!["a"];
    let list_b = list!["b"];
    let list_b_sync = list_sync!["b"];

    assert!(list_a == list_a_sync);
    assert!(list_a != list_b_sync);
    assert!(list_b == list_b_sync);
}

#[test]
fn test_partial_ord() {
    let list_1 = list!["a"];
    let list_1_prime = list!["a"];
    let list_2 = list!["b"];
    let list_3 = list![0.0];
    let list_4 = list![f32::NAN];

    assert_eq!(list_1.partial_cmp(&list_1_prime), Some(Ordering::Equal));
    assert_eq!(list_1.partial_cmp(&list_2), Some(Ordering::Less));
    assert_eq!(list_2.partial_cmp(&list_1), Some(Ordering::Greater));
    assert_eq!(list_3.partial_cmp(&list_4), None);
}

#[test]
fn test_ord() {
    let list_1 = list!["a"];
    let list_1_prime = list!["a"];
    let list_2 = list!["b"];

    assert_eq!(list_1.cmp(&list_1_prime), Ordering::Equal);
    assert_eq!(list_1.cmp(&list_2), Ordering::Less);
    assert_eq!(list_2.cmp(&list_1), Ordering::Greater);
}

#[test]
fn test_ord_pointer_kind_consistent() {
    let list_a = list!["a"];
    let list_a_sync = list_sync!["a"];
    let list_b = list!["b"];
    let list_b_sync = list_sync!["b"];

    assert!(list_a <= list_a_sync);
    assert!(list_a < list_b_sync);
    assert!(list_b >= list_b_sync);

    assert!(list_a_sync >= list_a);
    assert!(list_b_sync > list_a);
    assert!(list_b_sync <= list_b);
}

fn hash<T: Hash, P: SharedPointerKind>(list: &List<T, P>) -> u64 {
    #[allow(deprecated)]
    let mut hasher = core::hash::SipHasher::new();

    list.hash(&mut hasher);

    hasher.finish()
}

#[test]
fn test_hash() {
    let list_1 = list!["a"];
    let list_1_prime = list!["a"];
    let list_2 = list!["a", "b"];

    assert_eq!(hash(&list_1), hash(&list_1));
    assert_eq!(hash(&list_1), hash(&list_1_prime));
    assert_ne!(hash(&list_1), hash(&list_2));
}

#[test]
fn test_hash_pointer_kind_consistent() {
    let list = list!["a"];
    let list_sync = list_sync!["a"];

    assert_eq!(hash(&list), hash(&list_sync));
}

#[test]
fn test_clone() {
    let list = list!["hello", "there"];
    let clone = list.clone();

    assert!(clone.iter().eq(list.iter()));
    assert_eq!(clone.len(), list.len());
    assert_eq!(clone.last(), list.last());
}

#[allow(clippy::many_single_char_names)]
#[test]
fn test_drop_list() {
    // When it is dropped, it will set the variable it owned to false.
    use core::cell::Cell;

    struct DropStruct<'a>(&'a Cell<bool>);

    impl Drop for DropStruct<'_> {
        fn drop(&mut self) {
            self.0.set(false);
        }
    }

    // test that we actually dropped the elements
    let (a, b, c, d, e) =
        (Cell::new(true), Cell::new(true), Cell::new(true), Cell::new(true), Cell::new(true));

    let mut x = List::new();
    x.push_front_mut(DropStruct(&a));
    x.push_front_mut(DropStruct(&b));
    x.push_front_mut(DropStruct(&c));

    assert_eq!(
        vec![a.get(), b.get(), c.get(), d.get(), e.get()],
        vec![true, true, true, true, true]
    );

    let x2 = x.drop_first().unwrap().drop_first().unwrap();

    drop(x);
    assert_eq!(
        vec![a.get(), b.get(), c.get(), d.get(), e.get()],
        vec![true, false, false, true, true]
    );

    let y = x2.push_front(DropStruct(&d));

    drop(x2);
    assert_eq!(
        vec![a.get(), b.get(), c.get(), d.get(), e.get()],
        vec![true, false, false, true, true]
    );

    let z = y.push_front(DropStruct(&e));

    drop(y);
    assert_eq!(
        vec![a.get(), b.get(), c.get(), d.get(), e.get()],
        vec![true, false, false, true, true]
    );

    drop(z);
    assert_eq!(
        vec![a.get(), b.get(), c.get(), d.get(), e.get()],
        vec![false, false, false, false, false]
    );
}

#[test]
fn test_drop_large() {
    let limit = 1024 * 1024;
    let mut list = List::new();
    for i in 0..limit {
        list.push_front_mut(i);
    }
}

#[cfg(feature = "serde")]
#[test]
fn test_serde() {
    let list: List<i32> = list![5, 6, 7, 8];
    let encoded = serde_json::to_string(&list).unwrap();
    let decoded: List<i32> = serde_json::from_str(&encoded).unwrap();

    assert_eq!(list, decoded);
}
