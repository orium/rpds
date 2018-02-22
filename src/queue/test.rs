/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use super::*;

mod lazily_reversed_list_iter {
    use super::*;

    #[test]
    fn test_iter() -> () {
        let list = List::new()
            .push_front(2)
            .push_front(1)
            .push_front(0);
        let mut iterator = LazilyReversedListIter::new(&list);

        assert_eq!(iterator.next().map(|v| **v), Some(2));
        assert_eq!(iterator.next().map(|v| **v), Some(1));
        assert_eq!(iterator.next().map(|v| **v), Some(0));
        assert_eq!(iterator.next(), None);

        let empty_list: List<i32> = List::new();
        let mut iterator = LazilyReversedListIter::new(&empty_list);

        assert_eq!(iterator.next(), None);
    }

    #[test]
    fn test_iter_size_hint() -> () {
        let list = List::new()
            .push_front(2)
            .push_front(1)
            .push_front(0);
        let mut iterator = LazilyReversedListIter::new(&list);

        assert_eq!(iterator.size_hint(), (3, Some(3)));
        iterator.next();

        assert_eq!(iterator.size_hint(), (2, Some(2)));
        iterator.next();

        assert_eq!(iterator.size_hint(), (1, Some(1)));
        iterator.next();

        assert_eq!(iterator.size_hint(), (0, Some(0)));

        let empty_list: List<i32> = List::new();
        let iterator = LazilyReversedListIter::new(&empty_list);

        assert_eq!(iterator.size_hint(), (0, Some(0)));
    }
}

mod iter {
    use super::*;

    #[test]
    fn test_iter() -> () {
        let queue = Queue::new()
            .enqueue(0)
            .enqueue(1)
            .dequeue().unwrap()
            .enqueue(2)
            .enqueue(3);
        let mut iterator = queue.iter();

        assert_eq!(iterator.next(), Some(&1));
        assert_eq!(iterator.next(), Some(&2));
        assert_eq!(iterator.next(), Some(&3));
        assert_eq!(iterator.next(), None);
    }

    #[test]
    fn test_iter_size_hint() -> () {
        let queue = Queue::new()
            .enqueue(0)
            .enqueue(1)
            .dequeue().unwrap()
            .enqueue(2)
            .enqueue(3);
        let mut iterator = queue.iter();

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
        let queue = Queue::new()
            .enqueue(0)
            .enqueue(1)
            .dequeue().unwrap()
            .enqueue(2)
            .enqueue(3);
        let mut expected = 1;
        let mut left = 3;

        for n in &queue {
            left -= 1;

            assert!(left >= 0);
            assert_eq!(*n, expected);

            expected += 1;
        }

        assert_eq!(left, 0);
    }
}

mod internal {
    use super::*;

    #[test]
    fn test_enqueue_dequeue() -> () {
        let queue = Queue::new()
            .enqueue(0)
            .enqueue(1)
            .enqueue(2)
            .enqueue(3);
        let queue_2 = Queue::new()
            .enqueue(0)
            .enqueue(1)
            .dequeue().unwrap()
            .enqueue(2)
            .enqueue(3);
        let queue_3 = Queue::new()
            .enqueue(0)
            .enqueue(1)
            .enqueue(2)
            .enqueue(3)
            .dequeue().unwrap();
        let list_3_2_1_0 = List::new().push_front(0).push_front(1).push_front(2).push_front(3);
        let list_3_2 = List::new().push_front(2).push_front(3);
        let list_1 = List::new().push_front(1);
        let list_1_2_3 = List::new().push_front(3).push_front(2).push_front(1);


        assert!(queue.out_list.is_empty());
        assert_eq!(queue.in_list, list_3_2_1_0);

        assert_eq!(queue_2.out_list, list_1);
        assert_eq!(queue_2.in_list, list_3_2);

        assert_eq!(queue_3.out_list, list_1_2_3);
        assert!(queue_3.in_list.is_empty());
    }
}

mod compile_time {
    use super::*;

    #[test]
    fn test_is_send() -> () {
        let _: Box<Send> = Box::new(Queue::<i32>::new());
    }

    #[test]
    fn test_is_sync() -> () {
        let _: Box<Sync> = Box::new(Queue::<i32>::new());
    }
}

#[test]
fn test_new() -> () {
    let empty_queue: Queue<i32> = Queue::new();

    assert!(empty_queue.in_list.is_empty());
    assert!(empty_queue.out_list.is_empty());

    assert_eq!(empty_queue.len(), 0);
    assert!(empty_queue.is_empty());
}

#[test]
fn test_macro_queue() -> () {
    let queue_1 = Queue::new()
        .enqueue(1);
    let queue_1_2_3 = Queue::new()
        .enqueue(1)
        .enqueue(2)
        .enqueue(3);

    assert_eq!(Queue::<u32>::new(), queue![]);
    assert_eq!(queue_1, queue![1]);
    assert_eq!(queue_1_2_3, queue![1, 2, 3]);
}

#[test]
fn test_peek() -> () {
    let empty_queue: Queue<i32> = Queue::new();
    let singleton_queue = Queue::new()
        .enqueue("hello");
    let queue = Queue::new()
        .enqueue(0)
        .enqueue(1)
        .enqueue(2)
        .enqueue(3);
    let queue_2 = Queue::new()
        .enqueue(0)
        .enqueue(1)
        .dequeue().unwrap()
        .enqueue(2)
        .enqueue(3);
    let queue_3 = Queue::new()
        .enqueue(0)
        .enqueue(1)
        .enqueue(2)
        .enqueue(3)
        .dequeue().unwrap();

    assert_eq!(empty_queue.peek(), None);
    assert_eq!(singleton_queue.peek(), Some(&"hello"));
    assert_eq!(queue.peek(), Some(&0));
    assert_eq!(queue_2.peek(), Some(&1));
    assert_eq!(queue_3.peek(), Some(&1));
}

#[test]
fn test_dequeue() -> () {
    let empty_queue: Queue<i32> = Queue::new();
    let singleton_queue = Queue::new()
        .enqueue("hello");
    let queue = Queue::new()
        .enqueue(0)
        .enqueue(1)
        .enqueue(2)
        .enqueue(3);
    let queue_2 = Queue::new()
        .enqueue(0)
        .enqueue(1)
        .dequeue().unwrap()
        .enqueue(2)
        .enqueue(3);
    let queue_3 = Queue::new()
        .enqueue(0)
        .enqueue(1)
        .enqueue(2)
        .enqueue(3)
        .dequeue().unwrap();

    assert!(empty_queue.dequeue().is_none());
    assert_eq!(singleton_queue.dequeue().unwrap().peek(), None);
    assert_eq!(queue.dequeue().unwrap().peek(), Some(&1));
    assert_eq!(queue_2.dequeue().unwrap().peek(), Some(&2));
    assert_eq!(queue_3.dequeue().unwrap().peek(), Some(&2));

    assert_eq!(queue.len(), 4);
    assert_eq!(queue.dequeue().unwrap().len(), 3);
    assert_eq!(queue_2.len(), 3);
    assert_eq!(queue_2.dequeue().unwrap().len(), 2);
    assert_eq!(queue_3.len(), 3);
    assert_eq!(queue_3.dequeue().unwrap().len(), 2);
}

#[test]
fn test_from_iterator() -> () {
    let vec: Vec<u32> = vec![10, 11, 12, 13];
    let queue: Queue<u32> = vec.iter().map(|v| *v).collect();

    assert!(vec.iter().eq(queue.iter()));
}

#[test]
fn test_default() -> () {
    let queue: Queue<i32> = Queue::default();

    assert_eq!(queue.peek(), None);
    assert!(queue.is_empty());
}

#[test]
fn test_display() -> () {
    let empty_queue: Queue<i32> = Queue::new();
    let singleton_queue = Queue::new()
        .enqueue("hello");
    let queue = Queue::new()
        .enqueue(0)
        .enqueue(1)
        .enqueue(2)
        .enqueue(3);

    assert_eq!(format!("{}", empty_queue), "Queue()");
    assert_eq!(format!("{}", singleton_queue), "Queue(hello)");
    assert_eq!(format!("{}", queue), "Queue(0, 1, 2, 3)");
}

#[test]
fn test_eq() -> () {
    let queue_1 = Queue::new()
        .enqueue("a")
        .enqueue("a");
    let queue_1_prime = Queue::new()
        .enqueue("a")
        .enqueue("a");
    let queue_2 = Queue::new()
        .enqueue("a")
        .enqueue("b");

    assert_ne!(queue_1, queue_2);
    assert_eq!(queue_1, queue_1);
    assert_eq!(queue_1, queue_1_prime);
    assert_eq!(queue_2, queue_2);
}

#[test]
fn test_partial_ord() -> () {
    let queue_1 = Queue::new()
        .enqueue("a");
    let queue_1_prime = Queue::new()
        .enqueue("a");
    let queue_2 = Queue::new()
        .enqueue("b");
    let queue_3 = Queue::new()
        .enqueue(0.0);
    let queue_4 = Queue::new()
        .enqueue(::std::f32::NAN);

    assert_eq!(queue_1.partial_cmp(&queue_1_prime), Some(Ordering::Equal));
    assert_eq!(queue_1.partial_cmp(&queue_2), Some(Ordering::Less));
    assert_eq!(queue_2.partial_cmp(&queue_1), Some(Ordering::Greater));
    assert_eq!(queue_3.partial_cmp(&queue_4), None);
}

#[test]
fn test_ord() -> () {
    let queue_1 = Queue::new()
        .enqueue("a");
    let queue_1_prime = Queue::new()
        .enqueue("a");
    let queue_2 = Queue::new()
        .enqueue("b");

    assert_eq!(queue_1.cmp(&queue_1_prime), Ordering::Equal);
    assert_eq!(queue_1.cmp(&queue_2), Ordering::Less);
    assert_eq!(queue_2.cmp(&queue_1), Ordering::Greater);
}

fn hash<T: Hash>(queue: &Queue<T>) -> u64 {
    let mut hasher = ::std::collections::hash_map::DefaultHasher::new();

    queue.hash(&mut hasher);

    hasher.finish()
}

#[test]
fn test_hash() -> () {
    let queue_1 = Queue::new()
        .enqueue("a");
    let queue_1_prime = Queue::new()
        .enqueue("a");
    let queue_2 = Queue::new()
        .enqueue("a")
        .enqueue("b");

    assert_eq!(hash(&queue_1), hash(&queue_1));
    assert_eq!(hash(&queue_1), hash(&queue_1_prime));
    assert_ne!(hash(&queue_1), hash(&queue_2));
}

#[test]
fn test_clone() -> () {
    let queue = Queue::new()
        .enqueue("there")
        .enqueue("hello");
    let clone = queue.clone();

    assert!(clone.iter().eq(queue.iter()));
    assert_eq!(clone.len(), queue.len());
}

#[cfg(feature = "serde")]
#[test]
fn test_serde() -> () {
    use bincode::{serialize, deserialize};
    let queue: Queue<i32> = Queue::from_iter(vec![5,6,7,8].into_iter());
    let encoded = serialize(&queue).unwrap();
    let decoded: Queue<i32> = deserialize(&encoded).unwrap();
    assert_eq!(queue, decoded);
}
