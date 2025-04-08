/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use super::*;
use pretty_assertions::assert_eq;
use static_assertions::assert_impl_all;

assert_impl_all!(QueueSync<i32>: Send, Sync);

#[allow(dead_code)]
fn compile_time_macro_queue_sync_is_send_and_sync() -> impl Send + Sync {
    queue_sync!(0)
}

mod lazily_reversed_list_iter {
    use super::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_iter() {
        let list = list![0, 1, 2];
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
    fn test_iter_size_hint() {
        let list = list![0, 1, 2];
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
    use pretty_assertions::assert_eq;

    #[test]
    fn test_iter() {
        let mut queue = Queue::new();
        queue.enqueue_mut(0);
        queue.enqueue_mut(1);
        queue.dequeue_mut();
        queue.enqueue_mut(2);
        queue.enqueue_mut(3);
        let mut iterator = queue.iter();

        assert_eq!(iterator.next(), Some(&1));
        assert_eq!(iterator.next(), Some(&2));
        assert_eq!(iterator.next(), Some(&3));
        assert_eq!(iterator.next(), None);
    }

    #[test]
    fn test_iter_size_hint() {
        let mut queue = Queue::new();
        queue.enqueue_mut(0);
        queue.enqueue_mut(1);
        queue.dequeue_mut();
        queue.enqueue_mut(2);
        queue.enqueue_mut(3);
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
    fn test_into_iterator() {
        let mut queue = Queue::new();
        queue.enqueue_mut(0);
        queue.enqueue_mut(1);
        queue.dequeue_mut();
        queue.enqueue_mut(2);
        queue.enqueue_mut(3);
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
    use pretty_assertions::assert_eq;

    #[test]
    fn test_enqueue_dequeue_mut() {
        let queue = queue![0, 1, 2, 3];
        let mut queue_2 = Queue::new();
        queue_2.enqueue_mut(0);
        queue_2.enqueue_mut(1);
        queue_2.dequeue_mut();
        queue_2.enqueue_mut(2);
        queue_2.enqueue_mut(3);
        let mut queue_3 = Queue::new();
        queue_3.enqueue_mut(0);
        queue_3.enqueue_mut(1);
        queue_3.enqueue_mut(2);
        queue_3.enqueue_mut(3);
        queue_3.dequeue_mut();
        let list_3_2_1_0 = list![3, 2, 1, 0];
        let list_3_2 = list![3, 2];
        let list_1 = list![1];
        let list_1_2_3 = list![1, 2, 3];

        assert!(queue.out_list.is_empty());
        assert_eq!(queue.in_list, list_3_2_1_0);

        assert_eq!(queue_2.out_list, list_1);
        assert_eq!(queue_2.in_list, list_3_2);

        assert_eq!(queue_3.out_list, list_1_2_3);
        assert!(queue_3.in_list.is_empty());
    }
}

#[test]
fn test_new() {
    let empty_queue: Queue<i32> = Queue::new();

    assert!(empty_queue.in_list.is_empty());
    assert!(empty_queue.out_list.is_empty());

    assert_eq!(empty_queue.len(), 0);
    assert!(empty_queue.is_empty());
}

#[test]
fn test_macro_queue() {
    let mut queue_1 = Queue::new();
    queue_1.enqueue_mut(1);
    let mut queue_1_2_3 = Queue::new();
    queue_1_2_3.enqueue_mut(1);
    queue_1_2_3.enqueue_mut(2);
    queue_1_2_3.enqueue_mut(3);

    assert_eq!(Queue::<u32>::new(), queue![]);
    assert_eq!(queue_1, queue![1]);
    assert_eq!(queue_1_2_3, queue![1, 2, 3]);
}

#[test]
fn test_peek() {
    let empty_queue: Queue<i32> = Queue::new();
    let singleton_queue = queue!["hello"];
    let queue = queue![0, 1, 2, 3];
    let mut queue_2 = Queue::new();
    queue_2.enqueue_mut(0);
    queue_2.enqueue_mut(1);
    queue_2.dequeue_mut();
    queue_2.enqueue_mut(2);
    queue_2.enqueue_mut(3);
    let mut queue_3 = Queue::new();
    queue_3.enqueue_mut(0);
    queue_3.enqueue_mut(1);
    queue_3.enqueue_mut(2);
    queue_3.enqueue_mut(3);
    queue_3.dequeue_mut();

    assert_eq!(empty_queue.peek(), None);
    assert_eq!(singleton_queue.peek(), Some(&"hello"));
    assert_eq!(queue.peek(), Some(&0));
    assert_eq!(queue_2.peek(), Some(&1));
    assert_eq!(queue_3.peek(), Some(&1));
}

#[test]
fn test_dequeue_mut() {
    let mut empty_queue: Queue<i32> = Queue::new();
    let mut singleton_queue = queue!["hello"];
    let mut queue = queue![0, 1, 2, 3];
    let mut queue_2 = Queue::new();
    queue_2.enqueue_mut(0);
    queue_2.enqueue_mut(1);
    queue_2.dequeue_mut();
    queue_2.enqueue_mut(2);
    queue_2.enqueue_mut(3);
    let mut queue_3 = Queue::new();
    queue_3.enqueue_mut(0);
    queue_3.enqueue_mut(1);
    queue_3.enqueue_mut(2);
    queue_3.enqueue_mut(3);
    queue_3.dequeue_mut();

    empty_queue.dequeue_mut();
    assert!(empty_queue.is_empty());

    singleton_queue.dequeue_mut();
    assert_eq!(singleton_queue.peek(), None);

    queue.dequeue_mut();
    assert_eq!(queue.peek(), Some(&1));

    queue_2.dequeue_mut();
    assert_eq!(queue_2.peek(), Some(&2));

    queue_3.dequeue_mut();
    assert_eq!(queue_3.peek(), Some(&2));
}

#[test]
fn test_dequeue_mut_maintains_len() {
    let mut queue = queue![0, 1, 2, 3];
    let mut queue_2 = Queue::new();
    queue_2.enqueue_mut(0);
    queue_2.enqueue_mut(1);
    queue_2.dequeue_mut();
    queue_2.enqueue_mut(2);
    queue_2.enqueue_mut(3);
    let mut queue_3 = Queue::new();
    queue_3.enqueue_mut(0);
    queue_3.enqueue_mut(1);
    queue_3.enqueue_mut(2);
    queue_3.enqueue_mut(3);
    queue_3.dequeue_mut();

    assert_eq!(queue.len(), 4);
    queue.dequeue_mut();
    assert_eq!(queue.len(), 3);

    assert_eq!(queue_2.len(), 3);
    queue_2.dequeue_mut();
    assert_eq!(queue_2.len(), 2);

    assert_eq!(queue_3.len(), 3);
    queue_3.dequeue_mut();
    assert_eq!(queue_3.len(), 2);
}

#[test]
fn test_dequeue() {
    let empty_queue: Queue<i32> = Queue::new();
    let singleton_queue = Queue::new().enqueue("hello");
    let queue = Queue::new().enqueue(0).enqueue(1).enqueue(2).enqueue(3);
    let queue_2 = Queue::new().enqueue(0).enqueue(1).dequeue().unwrap().enqueue(2).enqueue(3);
    let queue_3 = Queue::new().enqueue(0).enqueue(1).enqueue(2).enqueue(3).dequeue().unwrap();

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
fn test_from_iterator() {
    let vec: Vec<u32> = vec![10, 11, 12, 13];
    let queue: Queue<u32> = vec.iter().copied().collect();

    assert!(vec.iter().eq(queue.iter()));
}

#[test]
fn test_default() {
    let queue: Queue<i32> = Queue::default();

    assert_eq!(queue.peek(), None);
    assert!(queue.is_empty());
}

#[test]
fn test_display() {
    let empty_queue: Queue<i32> = Queue::new();
    let singleton_queue = queue!["hello"];
    let queue = queue![0, 1, 2, 3];

    assert_eq!(format!("{}", empty_queue), "Queue()");
    assert_eq!(format!("{}", singleton_queue), "Queue(hello)");
    assert_eq!(format!("{}", queue), "Queue(0, 1, 2, 3)");
}

#[test]
fn test_eq() {
    let queue_1 = queue!["a", "a"];
    let queue_1_prime = queue!["a", "a"];
    let queue_2 = queue!["a", "b"];

    assert_ne!(queue_1, queue_2);
    assert_eq!(queue_1, queue_1);
    assert_eq!(queue_1, queue_1_prime);
    assert_eq!(queue_2, queue_2);
}

#[test]
fn test_eq_pointer_kind_consistent() {
    let queue_a = queue!["a"];
    let queue_a_sync = queue_sync!["a"];
    let queue_b = queue!["b"];
    let queue_b_sync = queue_sync!["b"];

    assert!(queue_a == queue_a_sync);
    assert!(queue_a != queue_b_sync);
    assert!(queue_b == queue_b_sync);
}

#[test]
fn test_partial_ord() {
    let queue_1 = queue!["a"];
    let queue_1_prime = queue!["a"];
    let queue_2 = queue!["b"];
    let queue_3 = queue![0.0];
    let queue_4 = queue![f32::NAN];

    assert_eq!(queue_1.partial_cmp(&queue_1_prime), Some(Ordering::Equal));
    assert_eq!(queue_1.partial_cmp(&queue_2), Some(Ordering::Less));
    assert_eq!(queue_2.partial_cmp(&queue_1), Some(Ordering::Greater));
    assert_eq!(queue_3.partial_cmp(&queue_4), None);
}

#[test]
fn test_ord() {
    let queue_1 = queue!["a"];
    let queue_1_prime = queue!["a"];
    let queue_2 = queue!["b"];

    assert_eq!(queue_1.cmp(&queue_1_prime), Ordering::Equal);
    assert_eq!(queue_1.cmp(&queue_2), Ordering::Less);
    assert_eq!(queue_2.cmp(&queue_1), Ordering::Greater);
}

#[test]
fn test_ord_pointer_kind_consistent() {
    let queue_a = queue!["a"];
    let queue_a_sync = queue_sync!["a"];
    let queue_b = queue!["b"];
    let queue_b_sync = queue_sync!["b"];

    assert!(queue_a <= queue_a_sync);
    assert!(queue_a < queue_b_sync);
    assert!(queue_b >= queue_b_sync);

    assert!(queue_a_sync >= queue_a);
    assert!(queue_b_sync > queue_a);
    assert!(queue_b_sync <= queue_b);
}

fn hash<T: Hash, P: SharedPointerKind>(queue: &Queue<T, P>) -> u64 {
    #[allow(deprecated)]
    let mut hasher = core::hash::SipHasher::new();

    queue.hash(&mut hasher);

    hasher.finish()
}

#[test]
fn test_hash() {
    let queue_1 = queue!["a"];
    let queue_1_prime = queue!["a"];
    let queue_2 = queue!["a", "b"];

    assert_eq!(hash(&queue_1), hash(&queue_1));
    assert_eq!(hash(&queue_1), hash(&queue_1_prime));
    assert_ne!(hash(&queue_1), hash(&queue_2));
}

#[test]
fn test_hash_pointer_kind_consistent() {
    let queue = queue!["a"];
    let queue_sync = queue_sync!["a"];

    assert_eq!(hash(&queue), hash(&queue_sync));
}

#[test]
fn test_clone() {
    let queue = queue!["hello", "there"];
    let clone = queue.clone();

    assert!(clone.iter().eq(queue.iter()));
    assert_eq!(clone.len(), queue.len());
}

#[cfg(feature = "serde")]
#[test]
fn test_serde() {
    let queue: Queue<i32> = queue![5, 6, 7, 8];
    let encoded = serde_json::to_string(&queue).unwrap();
    let decoded: Queue<i32> = serde_json::from_str(&encoded).unwrap();

    assert_eq!(queue, decoded);
}
