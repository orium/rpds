/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

#![allow(clippy::cast_possible_truncation)]
#![allow(clippy::cast_possible_wrap)]
#![allow(clippy::cast_sign_loss)]

use super::*;
use alloc::string::String;
use pretty_assertions::assert_eq;
use static_assertions::assert_impl_all;

assert_impl_all!(VectorSync<i32>: Send, Sync);

#[allow(dead_code)]
fn compile_time_macro_vector_sync_is_send_and_sync() -> impl Send + Sync {
    vector_sync!(0)
}

impl<T: PartialEq, P> PartialEq for Node<T, P>
where
    P: SharedPointerKind,
{
    fn eq(&self, other: &Node<T, P>) -> bool {
        match (self, other) {
            (Node::Branch(v), Node::Branch(vo)) => v == vo,
            (Node::Leaf(v), Node::Leaf(vo)) => v == vo,
            _ => false,
        }
    }
}

impl<T: Eq, P> Eq for Node<T, P> where P: SharedPointerKind {}

mod node {
    use super::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_new_empty_branch() {
        let node: Node<u32> = Node::new_empty_branch();

        match node {
            Node::Branch(a) => {
                assert_eq!(a.len(), 0);
                assert_eq!(a.capacity(), 0, "Capacity of the branch array is wasteful");
            }
            Node::Leaf(_) => panic!("Invalid node type"),
        }
    }

    #[test]
    fn test_new_empty_leaf() {
        let node: Node<u32> = Node::new_empty_leaf();

        match node {
            Node::Leaf(a) => {
                assert_eq!(a.len(), 0);
                assert_eq!(a.capacity(), 0, "Capacity of the leaf array is wasteful");
            }
            Node::Branch(_) => panic!("Invalid node type"),
        }
    }

    #[test]
    fn test_drop_last_single_level() {
        let mut empty_leaf: Node<u32> = Node::new_empty_leaf();
        let mut empty_branch: Node<u32> = Node::new_empty_branch();
        let mut singleton_node: Node<u32> = vector![0].root.as_ref().clone();
        let mut one_level_node: Node<u32> = vector![0, 1].root.as_ref().clone();

        assert!(empty_leaf.drop_last());
        assert!(empty_branch.drop_last());
        assert!(singleton_node.drop_last());
        assert!(!one_level_node.drop_last());
        assert_eq!(one_level_node.used(), 1);
    }

    #[test]
    fn test_drop_last_multi_level() {
        let mut node_three: Node<u32> =
            Vector::new_with_bits(1).push_back(0).push_back(1).push_back(2).root.as_ref().clone();
        let mut node_four: Node<u32> = Vector::new_with_bits(1)
            .push_back(0)
            .push_back(1)
            .push_back(2)
            .push_back(3)
            .root
            .as_ref()
            .clone();

        let node_three_after_drop = {
            let a_leaf = vec![SharedPointer::new(0), SharedPointer::new(1)];

            let leaf = Node::Leaf(a_leaf);

            let a_branch = vec![SharedPointer::new(leaf)];

            Node::Branch(a_branch)
        };

        let node_four_after_drop = {
            let a_leaf_0 = vec![SharedPointer::new(0), SharedPointer::new(1)];

            let leaf_0 = Node::Leaf(a_leaf_0);

            let a_leaf_1 = {
                let mut a = Vec::with_capacity(2);
                a.push(SharedPointer::new(2));
                a
            };

            let leaf_1 = Node::Leaf(a_leaf_1);

            let a_branch = vec![SharedPointer::new(leaf_0), SharedPointer::new(leaf_1)];

            Node::Branch(a_branch)
        };

        assert!(!node_three.drop_last());
        assert_eq!(node_three, node_three_after_drop);
        assert!(!node_four.drop_last());
        assert_eq!(node_four, node_four_after_drop);
    }
}

mod iter {
    use super::*;
    use pretty_assertions::assert_eq;

    #[allow(clippy::explicit_iter_loop)]
    #[allow(clippy::never_loop)]
    #[test]
    fn test_iter_empty() {
        let vector: Vector<i32> = Vector::new();

        for _ in vector.iter() {
            panic!("iterator should be empty");
        }
    }

    #[allow(clippy::never_loop)]
    #[test]
    fn test_iter_empty_backwards() {
        let vector: Vector<i32> = Vector::new();

        for _ in vector.iter().rev() {
            panic!("iterator should be empty");
        }
    }

    #[allow(clippy::explicit_iter_loop)]
    #[test]
    fn test_iter_big_vector() {
        let limit = 32 * 32 * 32 + 1;
        let mut vector = Vector::new();
        let mut expected = 0;
        let mut left = limit;

        for i in 0..limit {
            vector = vector.push_back(i);
        }

        for v in vector.iter() {
            left -= 1;

            assert!(left >= 0);
            assert_eq!(*v, expected);

            expected += 1;
        }

        assert_eq!(left, 0);
    }

    #[test]
    fn test_iter_big_vector_backwards() {
        let limit = 32 * 32 * 32 + 1;
        let mut vector = Vector::new();
        let mut expected = limit - 1;
        let mut left = limit;

        for i in 0..limit {
            vector = vector.push_back(i);
        }

        for v in vector.iter().rev() {
            left -= 1;

            assert!(left >= 0);
            assert_eq!(*v, expected);

            expected -= 1;
        }

        assert_eq!(left, 0);
    }

    #[test]
    fn test_iter_backwards() {
        let vector = vector![0, 1, 2, 3];
        let mut expected = 3;
        let mut left = 4;

        for n in vector.iter().rev() {
            left -= 1;

            assert!(left >= 0);
            assert_eq!(*n, expected);

            expected -= 1;
        }

        assert_eq!(left, 0);
    }

    #[test]
    fn test_iter_both_directions() {
        let vector = vector![0, 1, 2, 3, 4, 5];
        let mut iterator = vector.iter();

        assert_eq!(iterator.next(), Some(&0));
        assert_eq!(iterator.next_back(), Some(&5));
        assert_eq!(iterator.next_back(), Some(&4));
        assert_eq!(iterator.next(), Some(&1));
        assert_eq!(iterator.next(), Some(&2));
        assert_eq!(iterator.next_back(), Some(&3));
        assert_eq!(iterator.next_back(), None);
        assert_eq!(iterator.next(), None);
    }

    #[test]
    fn test_iter_size_hint() {
        let vector = vector![0, 1, 2];
        let mut iterator = vector.iter();

        assert_eq!(iterator.size_hint(), (3, Some(3)));

        iterator.next();

        assert_eq!(iterator.size_hint(), (2, Some(2)));

        iterator.next_back();

        assert_eq!(iterator.size_hint(), (1, Some(1)));

        iterator.next_back();

        assert_eq!(iterator.size_hint(), (0, Some(0)));
    }

    #[test]
    fn test_into_iterator() {
        let vector = vector![0, 1, 2, 3];
        let mut left = 4;

        for (expected, n) in vector.into_iter().enumerate() {
            left -= 1;

            assert!(left >= 0);
            assert_eq!(*n, expected);
        }

        assert_eq!(left, 0);
    }
}

mod internal {
    use super::*;
    use pretty_assertions::assert_eq;

    fn dummy_vector_with_length(len: usize) -> Vector<u8> {
        let mut v = Vector::new_with_bits(5);
        v.length = len;
        v
    }

    #[test]
    fn test_degree() {
        use vector_utils::degree;

        assert_eq!(degree(1), 2);
        assert_eq!(degree(2), 4);
        assert_eq!(degree(3), 8);
        assert_eq!(degree(4), 16);
        assert_eq!(degree(5), 32);
    }

    #[test]
    fn test_height() {
        assert_eq!(dummy_vector_with_length(0).height(), 0);
        assert_eq!(dummy_vector_with_length(5).height(), 0);
        assert_eq!(dummy_vector_with_length(32).height(), 0);
        assert_eq!(dummy_vector_with_length(33).height(), 1);
        assert_eq!(dummy_vector_with_length(64).height(), 1);
        assert_eq!(dummy_vector_with_length(128).height(), 1);
        assert_eq!(dummy_vector_with_length(512).height(), 1);
        assert_eq!(dummy_vector_with_length(1024).height(), 1);
        assert_eq!(dummy_vector_with_length(1025).height(), 2);
        assert_eq!(dummy_vector_with_length(32_768).height(), 2);
        assert_eq!(dummy_vector_with_length(32_769).height(), 3);
        assert_eq!(dummy_vector_with_length(1_048_576).height(), 3);
        assert_eq!(dummy_vector_with_length(1_048_577).height(), 4);
    }

    #[test]
    fn test_mask() {
        use vector_utils::mask;

        assert_eq!(mask(1), 0b00001);
        assert_eq!(mask(2), 0b00011);
        assert_eq!(mask(3), 0b00111);
        assert_eq!(mask(4), 0b01111);
        assert_eq!(mask(5), 0b11111);
    }

    #[allow(clippy::unusual_byte_groupings)]
    #[test]
    fn test_bucket() {
        use vector_utils::bucket;

        assert_eq!(bucket(5, 0b_00100_00011_00010_00001, 0), 0b00001);
        assert_eq!(bucket(5, 0b_00100_00011_00010_00001, 1), 0b00010);
        assert_eq!(bucket(5, 0b_00100_00011_00010_00001, 2), 0b00011);
        assert_eq!(bucket(5, 0b_00100_00011_00010_00001, 3), 0b00100);
    }

    #[test]
    fn test_compress_root() {
        let empty_leaf: Node<u32> = Node::new_empty_leaf();
        let empty_branch: Node<u32> = Node::new_empty_branch();
        let singleton_leaf: Node<u32> = vector![0].root.as_ref().clone();
        let compressed_branch: Node<u32> =
            Vector::new_with_bits(1).push_back(0).push_back(1).push_back(3).root.as_ref().clone();
        let (uncompressed_branch, uncompressed_branch_leaf) = {
            let leaf: Node<_, RcK> =
                Vector::new_with_bits(1).push_back(0).push_back(1).root.as_ref().clone();

            let a_branch = {
                let mut a = Vec::with_capacity(2);
                a.push(SharedPointer::new(leaf.clone()));
                a
            };

            (Node::Branch(a_branch), leaf)
        };

        assert_eq!(Vector::compress_root(&mut empty_leaf.clone()), None);
        assert_eq!(Vector::compress_root(&mut empty_branch.clone()), None);
        assert_eq!(Vector::compress_root(&mut singleton_leaf.clone()), None);
        assert_eq!(Vector::compress_root(&mut compressed_branch.clone()), None);
        assert_eq!(
            Vector::compress_root(&mut uncompressed_branch.clone()),
            Some(SharedPointer::new(uncompressed_branch_leaf)),
        );
    }

    #[test]
    fn test_root_max_capacity() {
        assert_eq!(dummy_vector_with_length(0).root_max_capacity(), 32);
        assert_eq!(dummy_vector_with_length(5).root_max_capacity(), 32);
        assert_eq!(dummy_vector_with_length(32).root_max_capacity(), 32);
        assert_eq!(dummy_vector_with_length(33).root_max_capacity(), 1024);
        assert_eq!(dummy_vector_with_length(1024).root_max_capacity(), 1024);
        assert_eq!(dummy_vector_with_length(1025).root_max_capacity(), 32_768);
        assert_eq!(dummy_vector_with_length(32_768).root_max_capacity(), 32_768);
        assert_eq!(dummy_vector_with_length(32_769).root_max_capacity(), 1_048_576);
    }

    #[test]
    fn test_is_root_full() {
        assert!(!dummy_vector_with_length(0).is_root_full());
        assert!(!dummy_vector_with_length(5).is_root_full());
        assert!(dummy_vector_with_length(32).is_root_full());
        assert!(!dummy_vector_with_length(33).is_root_full());
        assert!(dummy_vector_with_length(1024).is_root_full());
        assert!(!dummy_vector_with_length(1025).is_root_full());
        assert!(dummy_vector_with_length(32_768).is_root_full());
        assert!(!dummy_vector_with_length(32_769).is_root_full());
    }
}

#[test]
fn test_macro_vector() {
    let vector_1 = Vector::new().push_back(1);
    let vector_1_2_3 = Vector::new().push_back(1).push_back(2).push_back(3);

    assert_eq!(Vector::<u32>::new(), vector![] as Vector<u32>);
    assert_eq!(vector_1, vector![1]);
    assert_eq!(vector_1_2_3, vector![1, 2, 3]);
}

#[test]
fn test_push_back_adds_element() {
    let limit = 32 * 32 * 32 + 1;
    let mut vector: Vector<i32> = Vector::new();

    for i in 0..limit {
        vector = vector.push_back(-i);
        assert_eq!(vector.get(i as usize), Some(&-i));
    }
}

#[test]
fn test_push_back_maintains_size() {
    let limit = 128;
    let mut vector: Vector<i32> = Vector::new();

    for i in 0..limit {
        assert_eq!(vector.len(), i as usize);
        vector = vector.push_back(-i);
    }

    assert_eq!(vector.len(), limit as usize);
}

#[test]
fn test_drop_last_drops_last_element() {
    let limit = 4 * 4 * 4 * 4 + 1;
    let mut vector: Vector<i32> = Vector::new_with_bits(2);
    let mut vectors = Vec::with_capacity(limit);

    for i in 0..limit {
        vector = vector.push_back(2 * i as i32);
        vectors.push(vector.clone());
    }

    for _ in 0..limit {
        let v = vectors.pop().unwrap();
        assert_eq!(vector, v);
        vector = vector.drop_last().unwrap();
    }

    assert_eq!(vector, Vector::<i32>::new());
}

#[test]
fn test_drop_last_keeps_vector_consistent() {
    let limit = 4 * 4 * 4 * 4 * 4 * 4 + 1;
    let mut vector: Vector<i32> = Vector::new_with_bits(2);

    for i in 0..limit {
        vector = vector.push_back(2 * i as i32);
    }

    for _ in 0..(limit / (4 * 4)) {
        vector = vector.drop_last().unwrap();
    }

    let new_len = limit - limit / (4 * 4);

    for i in 0..new_len {
        assert_eq!(vector.get(i).unwrap(), &(2 * i as i32));
    }

    assert_eq!(vector.get(new_len), None);
}

#[test]
fn test_drop_last_maintains_size() {
    let limit = 128;
    let mut vector: Vector<i32> = Vector::new();

    for i in 0..limit {
        vector = vector.push_back(-i);
    }

    for i in 0..limit {
        assert_eq!(vector.len(), (limit - i) as usize);
        vector = vector.drop_last().unwrap();
    }

    assert_eq!(vector.len(), 0);
}

#[test]
fn test_drop_last_on_empty_vector() {
    let vector: Vector<i32> = Vector::new();

    assert_eq!(vector.drop_last(), None);
}

#[test]
fn test_set_overwrites() {
    let limit = 32 * 32 + 1;
    let mut vector: Vector<i32> = Vector::new();

    for i in 0..limit {
        vector = vector.push_back(-i);
    }

    vector = vector.set(834, 0).unwrap();

    assert_eq!(vector.get(833), Some(&-833));
    assert_eq!(vector.get(834), Some(&0));
    assert_eq!(vector.get(835), Some(&-835));
    assert_eq!(vector.get(limit as usize), None);
}

#[test]
fn test_set_maintains_size() {
    let limit = 32 * 32 * 32;
    let mut vector: Vector<i32> = Vector::new();

    for i in 0..limit {
        vector = vector.push_back(-i);
    }

    for i in 0..limit {
        vector = vector.set(i as usize, i * i).unwrap();
        assert_eq!(vector.len(), limit as usize);
    }
}

#[test]
fn test_set_out_of_bounds() {
    let empty_vector: Vector<i32> = Vector::new();
    let singleton_vector: Vector<i32> = vector![0];

    assert_eq!(empty_vector.set(0, 0), None);
    assert_eq!(singleton_vector.set(1, 0), None);
}

#[test]
fn test_get() {
    let limit = 32 * 32 * 32 + 1;
    let mut vector = Vector::new();

    for i in 0..limit {
        vector = vector.push_back(i + 1);
    }

    assert_eq!(vector.get(0), Some(&1));
    assert_eq!(vector.get(2020), Some(&2021));
    assert_eq!(vector.get(limit - 1), Some(&limit));
    assert_eq!(vector.get(limit), None);
}

#[test]
fn test_index() {
    let vector = vector![10, 11, 12];

    assert_eq!(vector[0], 10);
    assert_eq!(vector[1], 11);
    assert_eq!(vector[2], 12);
}

#[test]
fn test_first() {
    let empty_vector: Vector<i32> = Vector::new();
    let vector = vector![1];

    assert_eq!(empty_vector.first(), None);
    assert_eq!(vector.first(), Some(&1));
}

#[test]
fn test_last() {
    let empty_vector: Vector<i32> = Vector::new();
    let vector = vector![1, 2];

    assert_eq!(empty_vector.last(), None);
    assert_eq!(vector.last(), Some(&2));
}

#[test]
fn test_from_iterator() {
    let vec: Vec<u32> = vec![10, 11, 12, 13];
    let vector: Vector<u32> = vec.iter().copied().collect();

    assert!(vec.iter().eq(vector.iter()));
}

#[test]
fn test_default() {
    let vector: Vector<i32> = Vector::default();

    assert_eq!(vector.len(), 0);
}

#[test]
fn test_display() {
    let empty_vector: Vector<i32> = Vector::new();
    let singleton_vector = vector!["hello"];
    let vector = vector![0, 1, 2, 3];

    assert_eq!(format!("{}", empty_vector), "[]");
    assert_eq!(format!("{}", singleton_vector), "[hello]");
    assert_eq!(format!("{}", vector), "[0, 1, 2, 3]");
}

#[test]
fn test_eq() {
    let vector_1 = vector!["a", "a"];
    let vector_1_prime = vector!["a", "a"];
    let vector_2 = vector!["a", "b"];
    let vector_3 = vector!["a", "b", "c"];

    assert_ne!(vector_1, vector_2);
    assert_ne!(vector_2, vector_3);
    assert_eq!(vector_1, vector_1);
    assert_eq!(vector_1, vector_1_prime);
    assert_eq!(vector_2, vector_2);

    // We also check this since `assert_ne!()` does not call `ne`.
    assert!(vector_1.ne(&vector_2));
    assert!(vector_2.ne(&vector_3));
}

#[test]
fn test_eq_pointer_kind_consistent() {
    let vector_a = vector!["a"];
    let vector_a_sync = vector_sync!["a"];
    let vector_b = vector!["b"];
    let vector_b_sync = vector_sync!["b"];

    assert!(vector_a == vector_a_sync);
    assert!(vector_a != vector_b_sync);
    assert!(vector_b == vector_b_sync);
}

#[test]
fn test_partial_ord() {
    let vector_1 = vector!["a"];
    let vector_1_prime = vector!["a"];
    let vector_2 = vector!["b"];
    let vector_3 = vector![0.0];
    let vector_4 = vector![f32::NAN];

    assert_eq!(vector_1.partial_cmp(&vector_1_prime), Some(Ordering::Equal));
    assert_eq!(vector_1.partial_cmp(&vector_2), Some(Ordering::Less));
    assert_eq!(vector_2.partial_cmp(&vector_1), Some(Ordering::Greater));
    assert_eq!(vector_3.partial_cmp(&vector_4), None);
}

#[test]
fn test_ord() {
    let vector_1 = vector!["a"];
    let vector_1_prime = vector!["a"];
    let vector_2 = vector!["b"];

    assert_eq!(vector_1.cmp(&vector_1_prime), Ordering::Equal);
    assert_eq!(vector_1.cmp(&vector_2), Ordering::Less);
    assert_eq!(vector_2.cmp(&vector_1), Ordering::Greater);
}

#[test]
fn test_ord_pointer_kind_consistent() {
    let vector_a = vector!["a"];
    let vector_a_sync = vector_sync!["a"];
    let vector_b = vector!["b"];
    let vector_b_sync = vector_sync!["b"];

    assert!(vector_a <= vector_a_sync);
    assert!(vector_a < vector_b_sync);
    assert!(vector_b >= vector_b_sync);

    assert!(vector_a_sync >= vector_a);
    assert!(vector_b_sync > vector_a);
    assert!(vector_b_sync <= vector_b);
}

fn hash<T: Hash, P: SharedPointerKind>(vector: &Vector<T, P>) -> u64 {
    #[allow(deprecated)]
    let mut hasher = core::hash::SipHasher::new();

    vector.hash(&mut hasher);

    hasher.finish()
}

#[test]
fn test_hash() {
    let vector_1 = vector!["a"];
    let vector_1_prime = vector!["a"];
    let vector_2 = vector!["a", "b"];

    assert_eq!(hash(&vector_1), hash(&vector_1));
    assert_eq!(hash(&vector_1), hash(&vector_1_prime));
    assert_ne!(hash(&vector_1), hash(&vector_2));
}

#[test]
fn test_hash_pointer_kind_consistent() {
    let vector = vector!["a"];
    let vector_sync = vector_sync!["a"];

    assert_eq!(hash(&vector), hash(&vector_sync));
}

#[test]
fn test_clone() {
    let vector = vector!["hello", "there"];
    let clone = vector.clone();

    assert_eq!(clone.len(), vector.len());
    assert!(clone.iter().eq(vector.iter()));
}

#[test]
fn test_index_mut() {
    let v1 = vector![
        String::from("This"),
        String::from("is"),
        String::from("where"),
        String::from("the"),
        String::from("fun"),
        String::from("begins!")
    ];
    let mut v2 = v1.clone();
    let expected1 = vector!["This", "is", "where", "the", "fun", "begins!"];
    let expected2 = vector!["That", "is", "where", "the", "cloning", "BEGINS!"];

    v2[0] = "That".into();
    v2[4] = String::from("cloning");
    v2[5].make_ascii_uppercase();

    let len = v2.len();
    assert_eq!(v2.get_mut(len), None);

    assert_eq!(v1, expected1);
    assert_eq!(v2, expected2);
}

#[cfg(feature = "serde")]
#[test]
fn test_serde() {
    let vector: Vector<i32> = vector![5, 6, 7, 8];
    let encoded = serde_json::to_string(&vector).unwrap();
    let decoded: Vector<i32> = serde_json::from_str(&encoded).unwrap();

    assert_eq!(vector, decoded);
}
