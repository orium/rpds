/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

#![allow(clippy::cast_possible_truncation)]
#![allow(clippy::cast_possible_wrap)]
#![allow(clippy::cast_sign_loss)]

use super::*;
use pretty_assertions::assert_eq;
use static_assertions::assert_impl_all;

assert_impl_all!(HashTrieMapSync<i32, i32>: Send, Sync);

#[allow(dead_code)]
fn compile_time_macro_hash_trie_map_sync_is_send_and_sync() -> impl Send + Sync {
    ht_map_sync!(0 => 0)
}

impl<K: PartialEq, V: PartialEq, P> PartialEq for Bucket<K, V, P>
where
    P: SharedPointerKind,
{
    fn eq(&self, other: &Bucket<K, V, P>) -> bool {
        match (self, other) {
            (Bucket::Single(self_entry), Bucket::Single(other_entry)) => self_entry.eq(other_entry),
            (Bucket::Collision(self_entry_list), Bucket::Collision(other_entry_list)) => {
                self_entry_list.eq(other_entry_list)
            }
            _ => false,
        }
    }
}

impl<K: Eq, V: Eq, P> Eq for Bucket<K, V, P> where P: SharedPointerKind {}

impl<K: PartialEq, V: PartialEq, P> PartialEq for EntryWithHash<K, V, P>
where
    P: SharedPointerKind,
{
    fn eq(&self, other: &EntryWithHash<K, V, P>) -> bool {
        self.entry.eq(&other.entry)
    }
}

impl<K: Eq, V: Eq, P> Eq for EntryWithHash<K, V, P> where P: SharedPointerKind {}

impl<K: PartialEq, V: PartialEq, P> PartialEq for Node<K, V, P>
where
    P: SharedPointerKind,
{
    fn eq(&self, other: &Node<K, V, P>) -> bool {
        match (self, other) {
            (Node::Branch(self_children), Node::Branch(other_children)) => {
                self_children.eq(other_children)
            }
            (Node::Leaf(self_bucket), Node::Leaf(other_bucket)) => self_bucket.eq(other_bucket),
            _ => false,
        }
    }
}

impl<K: Eq, V: Eq, P> Eq for Node<K, V, P> where P: SharedPointerKind {}

mod bucket {
    use super::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_list_remove_first() {
        use bucket_utils::list_remove_first;

        let list_a_b_c = list!['a', 'b', 'c'];
        let list_b_c = list!['b', 'c'];
        let list_a_c = list!['a', 'c'];
        let list_a_b = list!['a', 'b'];

        let mut list = list_a_b_c.clone();
        assert!(list_remove_first(&mut list, |_| false).is_none());
        assert_eq!(list, list_a_b_c);

        let mut list = list_a_b_c.clone();
        assert!(list_remove_first(&mut list, |c| *c == 'a').is_some());
        assert_eq!(list, list_b_c);

        let mut list = list_a_b_c.clone();
        assert!(list_remove_first(&mut list, |c| *c == 'b').is_some());
        assert_eq!(list, list_a_c);

        let mut list = list_a_b_c;
        assert!(list_remove_first(&mut list, |c| *c == 'c').is_some());
        assert_eq!(list, list_a_b);
    }

    #[test]
    fn test_get() {
        let hash_builder = crate::utils::DefaultBuildHasher::default();

        let entry_a: EntryWithHash<_, _> = EntryWithHash::new(0xAu8, 0, &hash_builder);
        let entry_b: EntryWithHash<_, _> = EntryWithHash::new(0xBu8, 1, &hash_builder);
        let entry_c: EntryWithHash<_, _> = EntryWithHash::new(0xCu8, 2, &hash_builder);

        let bucket_single = Bucket::Single(entry_a.clone());
        let bucket_collision = Bucket::Collision(list![entry_b.clone(), entry_a.clone()]);

        assert_eq!(bucket_single.get(entry_a.key(), entry_a.key_hash), Some(&entry_a));
        assert_eq!(bucket_single.get(entry_b.key(), entry_b.key_hash), None);

        assert_eq!(bucket_collision.get(entry_a.key(), entry_a.key_hash), Some(&entry_a));
        assert_eq!(bucket_collision.get(entry_b.key(), entry_b.key_hash), Some(&entry_b));
        assert_eq!(bucket_collision.get(entry_c.key(), entry_c.key_hash), None);
    }

    #[test]
    fn test_insert() {
        let hash_builder = crate::utils::DefaultBuildHasher::default();

        let entry_a: EntryWithHash<_, _> = EntryWithHash::new(0xAu8, 0, &hash_builder);
        let entry_a9: EntryWithHash<_, _> = EntryWithHash::new(0xAu8, 9, &hash_builder);
        let entry_b: EntryWithHash<_, _> = EntryWithHash::new(0xBu8, 1, &hash_builder);
        let entry_b9: EntryWithHash<_, _> = EntryWithHash::new(0xBu8, 9, &hash_builder);
        let entry_c: EntryWithHash<_, _> = EntryWithHash::new(0xCu8, 2, &hash_builder);
        let entry_d: EntryWithHash<_, _> = EntryWithHash::new(0xDu8, 2, &hash_builder);

        let bucket_single_a = Bucket::Single(entry_a.clone());
        let bucket_single_a9 = Bucket::Single(entry_a9.clone());
        let bucket_collision_b_a = Bucket::Collision(list![entry_b.clone(), entry_a.clone()]);
        let bucket_collision_a_b_c =
            Bucket::Collision(list![entry_a.clone(), entry_b.clone(), entry_c.clone()]);
        let bucket_collision_b9_a_c =
            Bucket::Collision(list![entry_b9.clone(), entry_a.clone(), entry_c.clone()]);
        let bucket_collision_d_a_b_c =
            Bucket::Collision(list![entry_d.clone(), entry_a, entry_b.clone(), entry_c]);

        // Note that we care about the position of the inserted entry: we want it to be in the
        // beginning of the list as to improve performance with high temporal locality (since
        // `get()` will try to match according to the list order).  The order of the rest of the
        // list must be preserved for the same reason.

        let mut bucket = bucket_single_a.clone();
        assert!(!bucket.insert(entry_a9));
        assert_eq!(bucket, bucket_single_a9);

        let mut bucket = bucket_single_a;
        assert!(bucket.insert(entry_b));
        assert_eq!(bucket, bucket_collision_b_a);

        let mut bucket = bucket_collision_a_b_c.clone();
        assert!(!bucket.insert(entry_b9));
        assert_eq!(bucket, bucket_collision_b9_a_c);

        let mut bucket = bucket_collision_a_b_c;
        assert!(bucket.insert(entry_d));
        assert_eq!(bucket, bucket_collision_d_a_b_c);
    }

    #[test]
    fn test_remove() {
        let hash_builder = crate::utils::DefaultBuildHasher::default();

        let entry_a: EntryWithHash<u8, i32> = EntryWithHash::new(0xAu8, 0, &hash_builder);
        let entry_b: EntryWithHash<u8, i32> = EntryWithHash::new(0xBu8, 1, &hash_builder);
        let entry_c: EntryWithHash<u8, i32> = EntryWithHash::new(0xCu8, 2, &hash_builder);
        let entry_d: EntryWithHash<u8, i32> = EntryWithHash::new(0xDu8, 2, &hash_builder);

        let bucket_single_a = Bucket::Single(entry_a.clone());
        let bucket_collision_b_c = Bucket::Collision(list![entry_b.clone(), entry_c.clone()]);
        let bucket_collision_a_b_c =
            Bucket::Collision(list![entry_a.clone(), entry_b.clone(), entry_c]);

        let mut bucket_ref: Option<&mut Bucket<u8, i32>> = None;
        assert!(!Bucket::remove(&mut bucket_ref, entry_a.key(), entry_a.key_hash));
        assert_eq!(bucket_ref, None);

        let mut bucket = bucket_single_a.clone();
        let mut bucket_ref = Some(&mut bucket);
        assert!(Bucket::remove(&mut bucket_ref, entry_a.key(), entry_a.key_hash));
        assert_eq!(bucket_ref, None);

        let mut bucket = bucket_single_a.clone();
        let mut bucket_ref = Some(&mut bucket);
        assert!(!Bucket::remove(&mut bucket_ref, entry_b.key(), entry_b.key_hash));
        assert_eq!(bucket_ref, Some(&mut bucket_single_a.clone()));

        let mut bucket = bucket_collision_a_b_c.clone();
        let mut bucket_ref = Some(&mut bucket);
        assert!(Bucket::remove(&mut bucket_ref, entry_a.key(), entry_a.key_hash));
        assert_eq!(bucket_ref, Some(&mut bucket_collision_b_c.clone()));

        let mut bucket = bucket_collision_a_b_c.clone();
        let mut bucket_ref = Some(&mut bucket);
        assert!(!Bucket::remove(&mut bucket_ref, entry_d.key(), entry_d.key_hash));
        assert_eq!(bucket_ref, Some(&mut bucket_collision_a_b_c.clone()));
    }
}

mod hasher_mocks {
    use super::*;
    use alloc::boxed::Box;
    use core::hash::Hasher;
    use std::collections::BTreeMap;

    pub struct MockedHashBuilder {
        byte_map: BTreeMap<u8, HashValue>,
    }

    pub struct MockedHasher {
        last_byte: Option<u8>,
        byte_map: BTreeMap<u8, HashValue>,
    }

    impl MockedHashBuilder {
        pub fn new(byte_map: BTreeMap<u8, HashValue>) -> MockedHashBuilder {
            MockedHashBuilder { byte_map }
        }
    }

    impl Clone for MockedHashBuilder {
        fn clone(&self) -> MockedHashBuilder {
            MockedHashBuilder::new(self.byte_map.clone())
        }
    }

    impl BuildHasher for MockedHashBuilder {
        type Hasher = MockedHasher;

        fn build_hasher(&self) -> MockedHasher {
            MockedHasher { last_byte: None, byte_map: self.byte_map.clone() }
        }
    }

    impl Hasher for MockedHasher {
        fn finish(&self) -> HashValue {
            *self.byte_map.get(self.last_byte.as_ref().unwrap()).unwrap()
        }

        fn write(&mut self, bytes: &[u8]) {
            self.last_byte = self.last_byte.or_else(|| bytes.last().copied());
        }
    }

    pub struct LimitedHashSpaceHashBuilder {
        inner_hash_builder: crate::utils::DefaultBuildHasher,
        hash_space_size: usize,
    }

    pub struct LimitedHashSpaceHasher {
        inner_hasher: Box<dyn core::hash::Hasher>,
        hash_space_size: usize,
    }

    impl LimitedHashSpaceHashBuilder {
        pub fn new(hash_space_size: usize) -> LimitedHashSpaceHashBuilder {
            LimitedHashSpaceHashBuilder {
                inner_hash_builder: crate::utils::DefaultBuildHasher::default(),
                hash_space_size,
            }
        }
    }

    impl Clone for LimitedHashSpaceHashBuilder {
        fn clone(&self) -> LimitedHashSpaceHashBuilder {
            LimitedHashSpaceHashBuilder {
                inner_hash_builder: self.inner_hash_builder.clone(),
                hash_space_size: self.hash_space_size,
            }
        }
    }

    impl BuildHasher for LimitedHashSpaceHashBuilder {
        type Hasher = LimitedHashSpaceHasher;

        fn build_hasher(&self) -> LimitedHashSpaceHasher {
            LimitedHashSpaceHasher {
                inner_hasher: Box::new(self.inner_hash_builder.build_hasher()),
                hash_space_size: self.hash_space_size,
            }
        }
    }

    impl Hasher for LimitedHashSpaceHasher {
        fn finish(&self) -> HashValue {
            self.inner_hasher.finish() % (self.hash_space_size as HashValue)
        }

        fn write(&mut self, bytes: &[u8]) {
            self.inner_hasher.write(bytes);
        }
    }
}

mod node {
    use super::*;
    use hasher_mocks::*;
    use pretty_assertions::assert_eq;
    use std::collections::BTreeMap;

    #[test]
    fn test_new_empty_branch() {
        let node: Node<u32, u32> = Node::new_empty_branch();

        match node {
            Node::Branch(array) => assert_eq!(array.size(), 0),
            Node::Leaf(_) => panic!("Invalid node type"),
        }
    }

    #[allow(clippy::unusual_byte_groupings)]
    #[allow(clippy::unreadable_literal)]
    #[test]
    fn test_index_from_hash() {
        let hash: HashValue = 0b_000100_100011_000010_100001 | (1 << 63);

        assert_eq!(node_utils::index_from_hash(hash, 0, 64), Some(0b100001));
        assert_eq!(node_utils::index_from_hash(hash, 1, 64), Some(0b000010));
        assert_eq!(node_utils::index_from_hash(hash, 2, 64), Some(0b100011));
        assert_eq!(node_utils::index_from_hash(hash, 3, 64), Some(0b000100));
        assert_eq!(node_utils::index_from_hash(hash, 10, 64), Some(0b001000));
        assert_eq!(node_utils::index_from_hash(hash, 11, 64), None);

        assert_eq!(node_utils::index_from_hash(hash, 15, 16), Some(0b1000));
        assert_eq!(node_utils::index_from_hash(hash, 16, 16), None);
    }

    fn dummy_hash_builder() -> MockedHashBuilder {
        let hash_mapping: BTreeMap<u8, HashValue> = [
            (0xA, 0b_0010_0110),
            (0xB, 0b_0001_0110),
            (0xC, 0b_0100_0010),
            (0xD, 0b_0000_1000 | (0b0111 << 60)),
            (0xE, 0b_0000_1000 | (0b0111 << 60)),
            (0x0, 0b_0000_1000 | (0b0111 << 60)),
            (0x1, 0b_0000_0110 | (0b0101 << 60)),
            (0x2, 0b_0000_1111 | (0b0111 << 60)),
        ]
        .iter()
        .copied()
        .collect();

        MockedHashBuilder::new(hash_mapping)
    }

    /// This constructs the following tree:
    ///
    /// ```text
    ///        0  ···  2  ···  6  ···  8  ···
    ///      ├───┼───┼───┼───┼───┼───┼───┼───┤
    ///      │ ∅ │ ∅ │ C │ ∅ │ • │ ∅ │ • │ ∅ │                depth 0
    ///      └───┴───┴───┴───┴─│─┴───┴─│─┴───┘
    ///                       ╱         ╲
    ///                      ╱           ╲
    ///                     ╱             ╲
    ///         0   1   2  ···            0   1   2  ···
    ///       ├───┼───┼───┼───┤         ├───┼───┼───┼───┤
    ///       │ ∅ │ B │ A │ ∅ │         │ • │ ∅ │ ∅ │ ∅ │     depth 1
    ///       └───┴───┴───┴───┘         └─│─┴───┴───┴───┘
    ///                                   │
    ///                                   ·
    ///                                   ·
    ///                                   ·
    ///                                   │
    ///                            0  ···   7   ···
    ///                          ├───┼───┼─────┼───┤
    ///                          │ ∅ │ ∅ │ D E │ ∅ │          depth 16 (maximum depth)
    ///                          └───┴───┴─────┴───┘
    /// ```
    fn dummy_hash_trie_map() -> HashTrieMap<u8, i32, RcK, MockedHashBuilder> {
        let hash_builder: MockedHashBuilder = dummy_hash_builder();

        let entry_a = EntryWithHash::new(0xAu8, 0, &hash_builder);
        let entry_b = EntryWithHash::new(0xBu8, 1, &hash_builder);
        let entry_c = EntryWithHash::new(0xCu8, 2, &hash_builder);
        let entry_d = EntryWithHash::new(0xDu8, 3, &hash_builder);
        let entry_e = EntryWithHash::new(0xEu8, 4, &hash_builder);

        let bucket_a = Bucket::Single(entry_a);
        let bucket_b = Bucket::Single(entry_b);
        let bucket_c = Bucket::Single(entry_c);
        let bucket_de = Bucket::Collision(list![entry_e, entry_d]);

        let node_depth_1_first = {
            let mut array = SparseArrayUsize::new();

            array.set(1, SharedPointer::new(Node::Leaf(bucket_b)));
            array.set(2, SharedPointer::new(Node::Leaf(bucket_a)));

            Node::Branch(array)
        };

        let node_maximum_depth = {
            let mut array = SparseArrayUsize::new();

            array.set(7, SharedPointer::new(Node::Leaf(bucket_de)));

            Node::Branch(array)
        };

        let maximum_depth_branch = {
            let mut branch = node_maximum_depth;

            for _ in 0..14 {
                let mut array = SparseArrayUsize::new();

                array.set(0, SharedPointer::new(branch));

                branch = Node::Branch(array);
            }

            branch
        };

        let node_root = {
            let mut array = SparseArrayUsize::new();

            array.set(2, SharedPointer::new(Node::Leaf(bucket_c)));
            array.set(6, SharedPointer::new(node_depth_1_first));
            array.set(8, SharedPointer::new(maximum_depth_branch));

            Node::Branch(array)
        };

        HashTrieMap {
            root: SharedPointer::new(node_root),
            size: 5,
            degree: 16,
            hasher_builder: hash_builder,
        }
    }

    #[test]
    fn test_get() {
        let map = dummy_hash_trie_map();

        assert_eq!(map.get(&0xA), Some(&0));
        assert_eq!(map.get(&0xB), Some(&1));
        assert_eq!(map.get(&0xC), Some(&2));
        assert_eq!(map.get(&0xD), Some(&3));
        assert_eq!(map.get(&0xE), Some(&4));
        assert_eq!(map.get(&0x0), None);
        assert_eq!(map.get(&0x1), None);
        assert_eq!(map.get(&0x2), None);
    }

    #[test]
    fn test_get_mut() {
        let original = dummy_hash_trie_map();
        let mut map = original.clone();

        *map.get_mut(&0xB).unwrap() = -1;
        *map.get_mut(&0xE).unwrap() = -1;
        assert!(map.get_mut(&0x1).is_none());
        assert!(map.get_mut(&0x2).is_none());

        assert_eq!(original.get(&0xA), Some(&0));
        assert_eq!(original.get(&0xB), Some(&1));
        assert_eq!(original.get(&0xC), Some(&2));
        assert_eq!(original.get(&0xD), Some(&3));
        assert_eq!(original.get(&0xE), Some(&4));
        assert_eq!(original.get(&0x0), None);
        assert_eq!(original.get(&0x1), None);
        assert_eq!(original.get(&0x2), None);

        assert_eq!(map.get(&0xA), Some(&0));
        assert_eq!(map.get(&0xB), Some(&-1));
        assert_eq!(map.get(&0xC), Some(&2));
        assert_eq!(map.get(&0xD), Some(&3));
        assert_eq!(map.get(&0xE), Some(&-1));
        assert_eq!(map.get(&0x0), None);
        assert_eq!(map.get(&0x1), None);
        assert_eq!(map.get(&0x2), None);
    }

    #[test]
    fn test_contains_key() {
        let map = dummy_hash_trie_map();

        assert!(map.contains_key(&0xA));
        assert!(map.contains_key(&0xE));
        assert!(!map.contains_key(&0x0));
    }

    #[test]
    fn test_insert() {
        let mut map: HashTrieMap<_, _, RcK, _> =
            HashTrieMap::new_with_hasher_and_degree_and_ptr_kind(dummy_hash_builder(), 16);

        assert_eq!(map.size(), 0);

        map = map.insert(0xA, 10);
        assert_eq!(map.size(), 1);

        map = map.insert(0xB, 1);
        assert_eq!(map.size(), 2);

        map = map.insert(0xC, 2);
        assert_eq!(map.size(), 3);

        map = map.insert(0xD, 3);
        assert_eq!(map.size(), 4);

        map = map.insert(0xE, 4);
        assert_eq!(map.size(), 5);

        map = map.insert(0xA, 0);
        assert_eq!(map.size(), 5);

        assert_eq!(map.get(&0xA), Some(&0));
        assert_eq!(map.get(&0xB), Some(&1));
        assert_eq!(map.get(&0xC), Some(&2));
        assert_eq!(map.get(&0xD), Some(&3));
        assert_eq!(map.get(&0xE), Some(&4));
        assert_eq!(map.get(&0x0), None);
        assert_eq!(map.get(&0x1), None);
        assert_eq!(map.get(&0x2), None);

        assert_eq!(map.root, dummy_hash_trie_map().root);
    }

    #[test]
    fn test_compress() {
        let hash_builder: MockedHashBuilder = dummy_hash_builder();

        let entry_a: EntryWithHash<_, _> = EntryWithHash::new(0xAu8, 0, &hash_builder);
        let entry_b: EntryWithHash<_, _> = EntryWithHash::new(0xBu8, 1, &hash_builder);

        let bucket_a = Bucket::Single(entry_a.clone());
        let bucket_b = Bucket::Single(entry_b.clone());
        let bucket_a_b = Bucket::Collision(list![entry_a, entry_b]);

        let empty_branch = Node::<u8, i32>::new_empty_branch();
        let branch_with_collision = {
            let mut array = SparseArrayUsize::new();

            array.set(4, SharedPointer::new(Node::Leaf(bucket_a_b.clone())));

            SharedPointer::<_, RcK>::new(Node::Branch(array))
        };
        let branch_with_two_subtrees = {
            let mut array = SparseArrayUsize::new();

            array.set(4, SharedPointer::new(Node::Leaf(bucket_a.clone())));
            array.set(7, SharedPointer::new(Node::Leaf(bucket_b.clone())));

            SharedPointer::<_, RcK>::new(Node::Branch(array))
        };
        let branch_with_single_bucket = {
            let mut array = SparseArrayUsize::new();

            array.set(4, SharedPointer::new(Node::Leaf(bucket_a.clone())));

            Node::Branch(array)
        };
        let branch_with_branch = {
            let mut array = SparseArrayUsize::new();

            array.set(4, SharedPointer::new(Node::<u8, i32>::new_empty_branch()));

            SharedPointer::<_, RcK>::new(Node::Branch(array))
        };
        let leaf_with_single_bucket_a = SharedPointer::<_, RcK>::new(Node::Leaf(bucket_a.clone()));
        let leaf_with_collision_bucket_a_b =
            SharedPointer::<_, RcK>::new(Node::Leaf(bucket_a_b.clone()));

        let mut node = Node::clone(&empty_branch);
        node.compress();
        assert_eq!(node, empty_branch);

        let mut node = Node::clone(&branch_with_collision);
        node.compress();
        assert_eq!(node, *branch_with_collision.borrow());

        let mut node = Node::clone(&branch_with_two_subtrees);
        node.compress();
        assert_eq!(node, *branch_with_two_subtrees.borrow());

        let mut node = Node::clone(&branch_with_single_bucket);
        node.compress();
        assert_eq!(node, *leaf_with_single_bucket_a.borrow());

        let mut node = Node::clone(&branch_with_branch);
        node.compress();
        assert_eq!(node, *branch_with_branch.borrow());

        let mut node = Node::clone(&leaf_with_single_bucket_a);
        node.compress();
        assert_eq!(node, *leaf_with_single_bucket_a.borrow());

        let mut node = Node::clone(&leaf_with_collision_bucket_a_b);
        node.compress();
        assert_eq!(node, *leaf_with_collision_bucket_a_b.borrow());
    }

    #[test]
    fn test_remove() {
        let map_a_b_c_d_e: HashTrieMap<_, _, RcK, _> =
            HashTrieMap::new_with_hasher_and_degree_and_ptr_kind(dummy_hash_builder(), 16)
                .insert(0xA, 0)
                .insert(0xB, 1)
                .insert(0xC, 2)
                .insert(0xD, 3)
                .insert(0xE, 4);
        let map_a_b_d_e: HashTrieMap<_, _, RcK, _> =
            HashTrieMap::new_with_hasher_and_degree_and_ptr_kind(dummy_hash_builder(), 16)
                .insert(0xA, 0)
                .insert(0xB, 1)
                .insert(0xD, 3)
                .insert(0xE, 4);
        let map_a_c_d_e: HashTrieMap<_, _, RcK, _> =
            HashTrieMap::new_with_hasher_and_degree_and_ptr_kind(dummy_hash_builder(), 16)
                .insert(0xA, 0)
                .insert(0xC, 2)
                .insert(0xD, 3)
                .insert(0xE, 4);
        let map_c_d_e: HashTrieMap<_, _, RcK, _> =
            HashTrieMap::new_with_hasher_and_degree_and_ptr_kind(dummy_hash_builder(), 16)
                .insert(0xC, 2)
                .insert(0xD, 3)
                .insert(0xE, 4);
        let map_a_b_c_e: HashTrieMap<_, _, RcK, _> =
            HashTrieMap::new_with_hasher_and_degree_and_ptr_kind(dummy_hash_builder(), 16)
                .insert(0xA, 0)
                .insert(0xB, 1)
                .insert(0xC, 2)
                .insert(0xE, 4);
        let map_a_b_c: HashTrieMap<_, _, RcK, _> =
            HashTrieMap::new_with_hasher_and_degree_and_ptr_kind(dummy_hash_builder(), 16)
                .insert(0xA, 0)
                .insert(0xB, 1)
                .insert(0xC, 2);
        let map_empty: HashTrieMap<_, _, RcK, _> =
            HashTrieMap::new_with_hasher_and_degree_and_ptr_kind(dummy_hash_builder(), 16);

        // Just a sanity check.
        assert_eq!(map_a_b_c_d_e.root, dummy_hash_trie_map().root);

        let removed_c = map_a_b_c_d_e.remove(&0xC);
        let removed_b = map_a_b_c_d_e.remove(&0xB);
        let removed_b_a = map_a_b_c_d_e.remove(&0xB).remove(&0xA);
        let removed_d = map_a_b_c_d_e.remove(&0xD);
        let removed_d_e = map_a_b_c_d_e.remove(&0xD).remove(&0xE);
        let removed_all =
            map_a_b_c_d_e.remove(&0xA).remove(&0xB).remove(&0xC).remove(&0xD).remove(&0xE);

        assert_eq!(removed_c.root, map_a_b_d_e.root);
        assert_eq!(removed_b.root, map_a_c_d_e.root);
        assert_eq!(removed_b_a.root, map_c_d_e.root);
        assert_eq!(removed_d.root, map_a_b_c_e.root);
        assert_eq!(removed_d_e.root, map_a_b_c.root);
        assert_eq!(removed_all.root, map_empty.root);

        assert_eq!(map_a_b_c_d_e.remove(&0x0).root, map_a_b_c_d_e.root);
        assert_eq!(map_a_b_c_d_e.remove(&0x1).root, map_a_b_c_d_e.root);
        assert_eq!(map_a_b_c_d_e.remove(&0x2).root, map_a_b_c_d_e.root);
    }
}

mod iter {
    use super::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_trie_max_height() {
        assert_eq!(iter_utils::trie_max_height(2), 64);
        assert_eq!(iter_utils::trie_max_height(16), 16);
        assert_eq!(iter_utils::trie_max_height(32), 13);
        assert_eq!(iter_utils::trie_max_height(64), 11);
    }

    #[allow(clippy::never_loop)]
    #[test]
    fn test_iter_empty() {
        let map: HashTrieMap<i32, i32> = HashTrieMap::new();

        for _ in map.iter() {
            panic!("iterator should be empty");
        }
    }

    fn iterator_test<H: BuildHasher + Clone>(initial_map: HashTrieMap<u32, i32, RcK, H>) {
        let mut map = initial_map;
        let limit: usize = 50_000;

        for i in 0..limit {
            map = map.insert(i as u32, -(i as i32));
        }

        let mut touched = vec![false; limit];

        for (k, v) in map.iter() {
            assert!(!touched[*k as usize]);

            assert_eq!(*k as i32, -*v);

            touched[*k as usize] = true;
        }

        assert!(touched.iter().all(|b| *b));
    }

    #[test]
    fn test_iter() {
        let degrees: Vec<u8> = [2, 4, 16, 32, DEFAULT_DEGREE]
            .into_iter()
            .filter(|d| *d <= DEFAULT_DEGREE) // we only want valid degrees
            .collect();

        for degree in degrees {
            iterator_test(HashTrieMap::new_with_degree(degree));
        }
    }

    #[test]
    fn test_iter_high_collision() {
        let degrees: Vec<u8> = [2, 4, 16, 32, DEFAULT_DEGREE]
            .into_iter()
            .filter(|d| *d <= DEFAULT_DEGREE) // we only want valid degrees
            .collect();

        for degree in degrees {
            let hasher = hasher_mocks::LimitedHashSpaceHashBuilder::new(1000);
            iterator_test(HashTrieMap::new_with_hasher_and_degree_and_ptr_kind(hasher, degree));
        }
    }

    #[test]
    fn test_iter_size_hint() {
        let map = ht_map![0 => 10, 1 => 11, 2 => 12];
        let mut iterator = map.iter();

        assert_eq!(iterator.size_hint(), (3, Some(3)));

        iterator.next();

        assert_eq!(iterator.size_hint(), (2, Some(2)));

        iterator.next();

        assert_eq!(iterator.size_hint(), (1, Some(1)));

        iterator.next();

        assert_eq!(iterator.size_hint(), (0, Some(0)));
    }

    #[test]
    fn test_iter_keys() {
        let map = ht_map![0 => 10, 1 => 11, 2 => 12];

        let mut touched = [false; 3];

        for k in map.keys() {
            assert!(!touched[*k as usize]);
            touched[*k as usize] = true;
        }

        assert!(touched.iter().all(|b| *b));
    }

    #[test]
    fn test_iter_values() {
        let map = ht_map![10 => 0, 11 => 1, 12 => 2];

        let mut touched = [false; 3];

        for v in map.values() {
            assert!(!touched[*v as usize]);
            touched[*v as usize] = true;
        }

        assert!(touched.iter().all(|b| *b));
    }

    #[test]
    fn test_into_iterator() {
        let map = ht_map![0 => 10, 1 => 11, 2 => 12];
        let mut left = 3;

        for _ in &map {
            left -= 1;
            assert!(left >= 0);
        }

        assert_eq!(left, 0);
    }
}

#[test]
fn test_macro_ht_map() {
    let map_1 = HashTrieMap::new().insert(1, 2);
    let map_1_2_3 = HashTrieMap::new().insert(1, 2).insert(2, 3).insert(3, 4);

    assert_eq!(HashTrieMap::<u32, u32>::new(), ht_map![]);
    assert_eq!(map_1, ht_map![1 => 2]);
    assert_eq!(map_1_2_3, ht_map![1 => 2, 2 => 3, 3 => 4]);
}

#[test]
fn test_get_key_value() {
    let mut map = HashTrieMap::new();

    map = map.insert("foo", 4);
    assert_eq!(map.get_key_value("foo"), Some((&"foo", &4)));

    map = map.insert("bar", 2);
    assert_eq!(map.get_key_value("foo"), Some((&"foo", &4)));
    assert_eq!(map.get_key_value("bar"), Some((&"bar", &2)));
}

#[test]
fn test_insert_simple() {
    let mut map = HashTrieMap::new();
    assert_eq!(map.size(), 0);

    map = map.insert("foo", 4);
    assert_eq!(map.size(), 1);
    assert_eq!(map.get("foo"), Some(&4));

    map = map.insert("bar", 2);
    assert_eq!(map.size(), 2);
    assert_eq!(map.get("foo"), Some(&4));
    assert_eq!(map.get("bar"), Some(&2));

    map = map.insert("baz", 12);
    assert_eq!(map.size(), 3);
    assert_eq!(map.get("foo"), Some(&4));
    assert_eq!(map.get("bar"), Some(&2));
    assert_eq!(map.get("baz"), Some(&12));

    map = map.insert("foo", 7);
    assert_eq!(map.size(), 3);
    assert_eq!(map.get("foo"), Some(&7));
    assert_eq!(map.get("bar"), Some(&2));
    assert_eq!(map.get("baz"), Some(&12));
}

fn insert_test<H: BuildHasher + Clone>(initial_map: HashTrieMap<u32, i32, RcK, H>) {
    let mut map = initial_map;

    // These are relatively small limits.  We prefer to do a more hardcore test in the mutable
    // version.
    let limit = 5_000;
    let overwrite_limit = 1_000;

    for i in 0..limit {
        map = map.insert(i, -(i as i32));

        assert_eq!(map.size(), (i as usize) + 1);
        assert_eq!(map.get(&i), Some(&-(i as i32)));

        // Lets also check a previous value.
        let prev_key = i / 2;
        assert_eq!(map.get(&prev_key), Some(&-(prev_key as i32)));
    }

    // Now we test some overwrites.

    for i in 0..overwrite_limit {
        assert_eq!(map.get(&i), Some(&-(i as i32)));

        map = map.insert(i, 2 * i as i32);

        assert_eq!(map.size(), limit as usize);
        assert_eq!(map.get(&i), Some(&(2 * i as i32)));
    }
}

#[test]
fn test_insert() {
    let degrees: Vec<u8> = [2, 4, 16, 32, DEFAULT_DEGREE]
        .into_iter()
        .filter(|d| *d <= DEFAULT_DEGREE) // we only want valid degrees
        .collect();

    for degree in degrees {
        insert_test(HashTrieMap::new_with_degree(degree));
    }
}

#[test]
fn test_insert_high_collision() {
    let degrees: Vec<u8> = [2, 4, 16, 32, DEFAULT_DEGREE]
        .into_iter()
        .filter(|d| *d <= DEFAULT_DEGREE) // we only want valid degrees
        .collect();

    for degree in degrees {
        let hasher = hasher_mocks::LimitedHashSpaceHashBuilder::new(1000);
        insert_test(HashTrieMap::new_with_hasher_and_degree_and_ptr_kind(hasher, degree));
    }
}

#[test]
fn test_insert_simple_mut() {
    let mut map = HashTrieMap::new();
    assert_eq!(map.size(), 0);

    map.insert_mut("foo", 4);
    assert_eq!(map.size(), 1);
    assert_eq!(map.get("foo"), Some(&4));

    map.insert_mut("bar", 2);
    assert_eq!(map.size(), 2);
    assert_eq!(map.get("foo"), Some(&4));
    assert_eq!(map.get("bar"), Some(&2));

    map.insert_mut("baz", 12);
    assert_eq!(map.size(), 3);
    assert_eq!(map.get("foo"), Some(&4));
    assert_eq!(map.get("bar"), Some(&2));
    assert_eq!(map.get("baz"), Some(&12));

    map.insert_mut("foo", 7);
    assert_eq!(map.size(), 3);
    assert_eq!(map.get("foo"), Some(&7));
    assert_eq!(map.get("bar"), Some(&2));
    assert_eq!(map.get("baz"), Some(&12));
}

fn insert_test_mut<H: BuildHasher + Clone>(initial_map: HashTrieMap<u32, i32, RcK, H>) {
    let mut map = initial_map;
    let limit = 25_000;
    let overwrite_limit = 5_000;

    for i in 0..limit {
        map.insert_mut(i, -(i as i32));

        assert_eq!(map.size(), (i as usize) + 1);
        assert_eq!(map.get(&i), Some(&-(i as i32)));

        // Lets also check a previous value.
        let prev_key = i / 2;
        assert_eq!(map.get(&prev_key), Some(&-(prev_key as i32)));
    }

    // Now we test some overwrites.

    for i in 0..overwrite_limit {
        assert_eq!(map.get(&i), Some(&-(i as i32)));

        map.insert_mut(i, 2 * i as i32);

        assert_eq!(map.size(), limit as usize);
        assert_eq!(map.get(&i), Some(&(2 * i as i32)));
    }
}

#[test]
fn test_insert_mut() {
    let degrees: Vec<u8> = [2, 4, 16, 32, DEFAULT_DEGREE]
        .into_iter()
        .filter(|d| *d <= DEFAULT_DEGREE) // we only want valid degrees
        .collect();

    for degree in degrees {
        insert_test_mut(HashTrieMap::new_with_degree(degree));
    }
}

#[test]
fn test_insert_high_collision_mut() {
    let degrees: Vec<u8> = [2, 4, 16, 32, DEFAULT_DEGREE]
        .into_iter()
        .filter(|d| *d <= DEFAULT_DEGREE) // we only want valid degrees
        .collect();

    for degree in degrees {
        let hasher = hasher_mocks::LimitedHashSpaceHashBuilder::new(1000);
        insert_test_mut(HashTrieMap::new_with_hasher_and_degree_and_ptr_kind(hasher, degree));
    }
}

#[test]
fn test_remove_simple() {
    let mut map = ht_map![
        "foo" => 4,
        "bar" => 12,
        "mumble" => 13,
        "baz" => 42
    ];
    let empty_map: HashTrieMap<i32, i32> = HashTrieMap::new();

    assert_eq!(empty_map.remove(&3), empty_map);

    assert_eq!(map.size(), 4);

    map = map.remove("not-there");
    assert_eq!(map.size(), 4);

    assert_eq!(map.get("foo"), Some(&4));
    assert_eq!(map.get("bar"), Some(&12));
    assert_eq!(map.get("mumble"), Some(&13));
    assert_eq!(map.get("baz"), Some(&42));

    map = map.remove("mumble");
    assert_eq!(map.size(), 3);

    assert_eq!(map.get("foo"), Some(&4));
    assert_eq!(map.get("bar"), Some(&12));
    assert_eq!(map.get("mumble"), None);
    assert_eq!(map.get("baz"), Some(&42));

    map = map.remove("foo");
    assert_eq!(map.size(), 2);

    assert_eq!(map.get("foo"), None);

    map = map.remove("baz");
    assert_eq!(map.size(), 1);

    assert_eq!(map.get("baz"), None);

    map = map.remove("bar");
    assert_eq!(map.size(), 0);

    assert_eq!(map.get("bar"), None);
}

fn remove_test<H: BuildHasher + Clone>(initial_map: HashTrieMap<u32, i32, RcK, H>) {
    let mut map = initial_map;

    // These are relatively small limits.  We prefer to do a more hardcore test in the mutable
    // version.
    let limit = 5_000;

    for i in 0..limit {
        map = map.insert(i, -(i as i32));
    }

    // Now lets remove half of it.

    for i in (0..limit / 2).map(|i| 2 * i) {
        assert_eq!(map.get(&i), Some(&-(i as i32)));

        map = map.remove(&i);

        assert!(!map.contains_key(&i));
        assert_eq!(map.size(), (limit - i / 2 - 1) as usize);

        // Also check than the previous one is ok.
        if i > 0 {
            assert_eq!(map.get(&(i - 1)), Some(&-((i - 1) as i32)));
        }
    }
}

#[test]
fn test_remove() {
    let degrees: Vec<u8> = [2, 4, 16, 32, DEFAULT_DEGREE]
        .into_iter()
        .filter(|d| *d <= DEFAULT_DEGREE) // we only want valid degrees
        .collect();

    for degree in degrees {
        remove_test(HashTrieMap::new_with_degree(degree));
    }
}

#[test]
fn test_remove_high_collision() {
    let degrees: Vec<u8> = [2, 4, 16, 32, DEFAULT_DEGREE]
        .into_iter()
        .filter(|d| *d <= DEFAULT_DEGREE) // we only want valid degrees
        .collect();

    for degree in degrees {
        let hasher = hasher_mocks::LimitedHashSpaceHashBuilder::new(1000);
        remove_test(HashTrieMap::new_with_hasher_and_degree_and_ptr_kind(hasher, degree));
    }
}

#[test]
fn test_remove_simple_mut() {
    let mut map = ht_map![
        "foo" => 4,
        "bar" => 12,
        "mumble" => 13,
        "baz" => 42
    ];

    assert_eq!(map.size(), 4);

    assert!(!map.remove_mut("not-there"));
    assert_eq!(map.size(), 4);

    assert_eq!(map.get("foo"), Some(&4));
    assert_eq!(map.get("bar"), Some(&12));
    assert_eq!(map.get("mumble"), Some(&13));
    assert_eq!(map.get("baz"), Some(&42));

    assert!(map.remove_mut("mumble"));
    assert_eq!(map.size(), 3);

    assert_eq!(map.get("foo"), Some(&4));
    assert_eq!(map.get("bar"), Some(&12));
    assert_eq!(map.get("mumble"), None);
    assert_eq!(map.get("baz"), Some(&42));

    assert!(map.remove_mut("foo"));
    assert_eq!(map.size(), 2);

    assert_eq!(map.get("foo"), None);

    assert!(map.remove_mut("baz"));
    assert_eq!(map.size(), 1);

    assert_eq!(map.get("baz"), None);

    assert!(map.remove_mut("bar"));
    assert_eq!(map.size(), 0);

    assert_eq!(map.get("bar"), None);
}

fn remove_test_mut<H: BuildHasher + Clone>(initial_map: HashTrieMap<u32, i32, RcK, H>) {
    let mut map = initial_map;
    let limit = 25_000;

    for i in 0..limit {
        map.insert_mut(i, -(i as i32));
    }

    // Now lets remove half of it.

    for i in (0..limit / 2).map(|i| 2 * i) {
        assert_eq!(map.get(&i), Some(&-(i as i32)));

        map.remove_mut(&i);

        assert!(!map.contains_key(&i));
        assert_eq!(map.size(), (limit - i / 2 - 1) as usize);

        // Also check than the previous one is ok.
        if i > 0 {
            assert_eq!(map.get(&(i - 1)), Some(&-((i - 1) as i32)));
        }
    }
}

#[test]
fn test_remove_mut() {
    let degrees: Vec<u8> = [2, 4, 16, 32, DEFAULT_DEGREE]
        .into_iter()
        .filter(|d| *d <= DEFAULT_DEGREE) // we only want valid degrees
        .collect();

    for degree in degrees {
        remove_test_mut(HashTrieMap::new_with_degree(degree));
    }
}

#[test]
fn test_remove_high_collision_mut() {
    let degrees: Vec<u8> = [2, 4, 16, 32, DEFAULT_DEGREE]
        .into_iter()
        .filter(|d| *d <= DEFAULT_DEGREE) // we only want valid degrees
        .collect();

    for degree in degrees {
        let hasher = hasher_mocks::LimitedHashSpaceHashBuilder::new(1000);
        remove_test_mut(HashTrieMap::new_with_hasher_and_degree_and_ptr_kind(hasher, degree));
    }
}

#[test]
fn test_index() {
    let map = ht_map![5 => "hello", 12 => "there"];

    assert_eq!(map[&5], "hello");
    assert_eq!(map[&12], "there");
}

#[test]
fn test_from_iterator() {
    let vec: Vec<(i32, &str)> = vec![(2, "two"), (5, "five")];
    let map: HashTrieMap<i32, &str> = vec.iter().copied().collect();
    let expected_map = ht_map![2 => "two", 5 => "five"];

    assert_eq!(map, expected_map);
}

#[test]
fn test_default() {
    let map: HashTrieMap<u32, char> = HashTrieMap::default();

    assert_eq!(map.size(), 0);
    assert!(map.is_empty());
}

#[test]
fn test_display() {
    let empty_map: HashTrieMap<i32, i32> = HashTrieMap::new();
    let singleton_map = ht_map!["hi" =>"hello"];
    let map = ht_map![5 => "hello", 12 => "there"];

    assert_eq!(format!("{}", empty_map), "{}");
    assert_eq!(format!("{}", singleton_map), "{hi: hello}");
    assert!(
        format!("{map}") == "{5: hello, 12: there}" || format!("{map}") == "{12: there, 5: hello}"
    );
}

#[test]
fn test_eq() {
    let map_1 = ht_map!["a" => 0xa, "b" => 0xb];
    let map_1_prime = ht_map!["a" => 0xa, "b" => 0xb];
    let map_1_prime_2 = ht_map!["a" => 0xa, "b" => 0xb, "b" => 0xb];
    let map_2 = ht_map!["a" => 0xa, "b" => 0xb + 1];
    let map_3 = ht_map!["a" => 0xa, "b" => 0xb + 1, "c" => 0xc];

    assert_eq!(map_1, map_1_prime);
    assert_eq!(map_1, map_1_prime_2);
    assert_eq!(map_1, map_1);
    assert_eq!(map_2, map_2);

    // We also check this since `assert_ne!()` does not call `ne`.
    assert!(map_1.ne(&map_2));
    assert!(map_2.ne(&map_3));
}

#[test]
fn test_eq_pointer_kind_consistent() {
    let map_a = ht_map!["a" => 0];
    let map_a_sync = ht_map_sync!["a" => 0];
    let map_b = ht_map!["b" => 1];
    let map_b_sync = ht_map_sync!["b" => 1];

    assert!(map_a == map_a_sync);
    assert!(map_a != map_b_sync);
    assert!(map_b == map_b_sync);
}

#[test]
fn test_clone() {
    let map = ht_map!["hello" => 4, "there" => 5];
    let clone = map.clone();

    assert_eq!(clone.size(), map.size());
    assert_eq!(clone.get("hello"), Some(&4));
    assert_eq!(clone.get("there"), Some(&5));
}

#[cfg(feature = "serde")]
#[test]
fn test_serde() {
    let map: HashTrieMap<i32, i32> = ht_map![5 => 6, 7 => 8, 9 => 10, 11 => 12];
    let encoded = serde_json::to_string(&map).unwrap();
    let decoded: HashTrieMap<i32, i32> = serde_json::from_str(&encoded).unwrap();

    assert_eq!(map, decoded);
}
