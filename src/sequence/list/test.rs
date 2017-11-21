/* This file is part of rpds.
 *
 * rpds is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * rpds is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with rpds.  If not, see <http://www.gnu.org/licenses/>.
 */

use super::*;

mod iter {
    use super::*;

    #[test]
    fn test_iter() -> () {
        let limit = 1024;
        let mut list = List::new();
        let mut left = limit;

        for i in 0..limit {
            list = list.push_front(i);
        }

        for v in list.iter() {
            left -= 1;
            assert_eq!(*v, left);
        }

        assert_eq!(left, 0);
    }

    #[test]
    fn test_iter_size_hint() -> () {
        let list = List::new()
            .push_front(2)
            .push_front(1)
            .push_front(0);
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
    fn test_into_iterator() -> () {
        let list = List::new()
            .push_front(3)
            .push_front(2)
            .push_front(1)
            .push_front(0);
        let mut expected = 0;
        let mut left = 4;

        for n in &list {
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
        let _: Box<Send> = Box::new(List::<i32>::new());
    }

    #[test]
    fn test_is_sync() -> () {
        let _: Box<Sync> = Box::new(List::<i32>::new());
    }
}

#[test]
fn test_new() -> () {
    let empty_list: List<i32> = List::new();

    match *empty_list.node {
        Node::Nil => (),
        _         => panic!("should be nil"),
    };

    assert_eq!(empty_list.len(), 0);
    assert!(empty_list.is_empty());
}

#[test]
fn test_head() -> () {
    let empty_list: List<i32> = List::new();
    let singleton_list = List::new()
        .push_front("hello");
    let list = List::new()
        .push_front(3)
        .push_front(2)
        .push_front(1)
        .push_front(0);

    assert_eq!(empty_list.first(), None);
    assert_eq!(singleton_list.first(), Some(&"hello"));
    assert_eq!(list.first(), Some(&0));
}

#[test]
fn test_tail() -> () {
    let empty_list: List<i32> = List::new();
    let singleton_list = List::new()
        .push_front("hello");
    let list = List::new()
        .push_front(3)
        .push_front(2)
        .push_front(1)
        .push_front(0);

    assert!(empty_list.drop_first().is_none());
    assert_eq!(singleton_list.drop_first().unwrap().first(), None);
    assert_eq!(list.drop_first().unwrap().first(), Some(&1));

    assert_eq!(list.len(), 4);
    assert_eq!(list.drop_first().unwrap().len(), 3);
}

#[test]
fn test_from_iterator() -> () {
    let vec: Vec<u32> = vec![10, 11, 12, 13];
    let list: List<u32> = vec.iter().map(|v| *v).collect();

    assert!(vec.iter().eq(list.iter()));
}

#[test]
fn test_default() -> () {
    let list: List<i32> = List::default();

    assert_eq!(list.first(), None);
    assert_eq!(list.len(), 0);
}

#[test]
fn test_display() -> () {
    let empty_list: List<i32> = List::new();
    let singleton_list = List::new()
        .push_front("hello");
    let list = List::new()
        .push_front(3)
        .push_front(2)
        .push_front(1)
        .push_front(0);

    assert_eq!(format!("{}", empty_list), "[]");
    assert_eq!(format!("{}", singleton_list), "[hello]");
    assert_eq!(format!("{}", list), "[0, 1, 2, 3]");
}

#[test]
fn test_eq() -> () {
    let list_1 = List::new()
        .push_front("a")
        .push_front("a");
    let list_1_prime = List::new()
        .push_front("a")
        .push_front("a");
    let list_2 = List::new()
        .push_front("b")
        .push_front("a");

    assert_ne!(list_1, list_2);
    assert_eq!(list_1, list_1);
    assert_eq!(list_1, list_1_prime);
    assert_eq!(list_2, list_2);
}

#[test]
fn test_partial_ord() -> () {
    let list_1 = List::new()
        .push_front("a");
    let list_1_prime = List::new()
        .push_front("a");
    let list_2 = List::new()
        .push_front("b");
    let list_3 = List::new()
        .push_front(0.0);
    let list_4 = List::new()
        .push_front(::std::f32::NAN);

    assert_eq!(list_1.partial_cmp(&list_1_prime), Some(Ordering::Equal));
    assert_eq!(list_1.partial_cmp(&list_2), Some(Ordering::Less));
    assert_eq!(list_2.partial_cmp(&list_1), Some(Ordering::Greater));
    assert_eq!(list_3.partial_cmp(&list_4), None);
}

#[test]
fn test_ord() -> () {
    let list_1 = List::new()
        .push_front("a");
    let list_1_prime = List::new()
        .push_front("a");
    let list_2 = List::new()
        .push_front("b");

    assert_eq!(list_1.cmp(&list_1_prime), Ordering::Equal);
    assert_eq!(list_1.cmp(&list_2), Ordering::Less);
    assert_eq!(list_2.cmp(&list_1), Ordering::Greater);
}

fn hash<T: Hash>(list: &List<T>) -> u64 {
    let mut hasher = ::std::collections::hash_map::DefaultHasher::new();

    list.hash(&mut hasher);

    hasher.finish()
}

#[test]
fn test_hash() -> () {
    let list_1 = List::new()
        .push_front("a");
    let list_1_prime = List::new()
        .push_front("a");
    let list_2 = List::new()
        .push_front("b")
        .push_front("a");

    assert_eq!(hash(&list_1), hash(&list_1));
    assert_eq!(hash(&list_1), hash(&list_1_prime));
    assert_ne!(hash(&list_1), hash(&list_2));
}

#[test]
fn test_clone() -> () {
    let list = List::new()
        .push_front("there")
        .push_front("hello");
    let clone = list.clone();

    assert!(clone.iter().eq(list.iter()));
    assert_eq!(clone.len(), list.len());
}
