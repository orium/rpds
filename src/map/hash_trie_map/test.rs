/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use super::*;

mod bucket {
    use super::*;

    #[test]
    fn test_list_remove_first() -> () {
        use self::bucket_utils::list_remove_first;

        let list_a_b_c = List::new()
            .push_front('c')
            .push_front('b')
            .push_front('a');
        let list_b_c = List::new()
            .push_front('c')
            .push_front('b');
        let list_a_c = List::new()
            .push_front('c')
            .push_front('a');
        let list_a_b = List::new()
            .push_front('b')
            .push_front('a');

        assert_eq!(list_remove_first(&list_a_b_c, |_| false), (list_a_b_c.clone(), false));
        assert_eq!(list_remove_first(&list_a_b_c, |c| *c == 'a'), (list_b_c, true));
        assert_eq!(list_remove_first(&list_a_b_c, |c| *c == 'b'), (list_a_c, true));
        assert_eq!(list_remove_first(&list_a_b_c, |c| *c == 'c'), (list_a_b, true));
    }

    #[test]
    fn test_get() -> () {
        let hash_builder = RandomState::new();

        let entry_a = EntryWithHash::new(0xAu8, 0, &hash_builder);
        let entry_b = EntryWithHash::new(0xBu8, 1, &hash_builder);
        let entry_c = EntryWithHash::new(0xCu8, 2, &hash_builder);

        let bucket_single = Bucket::Single(EntryWithHash::clone(&entry_a));
        let bucket_collision = Bucket::Collision(
            List::new()
                .push_front(EntryWithHash::clone(&entry_a))
                .push_front(EntryWithHash::clone(&entry_b))
        );

        assert_eq!(bucket_single.get(entry_a.key(), entry_a.key_hash), Some(entry_a.borrow()));
        assert_eq!(bucket_single.get(entry_b.key(), entry_b.key_hash), None);

        assert_eq!(bucket_collision.get(entry_a.key(), entry_a.key_hash), Some(entry_a.borrow()));
        assert_eq!(bucket_collision.get(entry_b.key(), entry_b.key_hash), Some(entry_b.borrow()));
        assert_eq!(bucket_collision.get(entry_c.key(), entry_c.key_hash), None);
    }

    #[test]
    fn test_insert() -> () {
        let hash_builder = RandomState::new();

        let entry_a  = EntryWithHash::new(0xAu8, 0, &hash_builder);
        let entry_a9 = EntryWithHash::new(0xAu8, 9, &hash_builder);
        let entry_b  = EntryWithHash::new(0xBu8, 1, &hash_builder);
        let entry_b9 = EntryWithHash::new(0xBu8, 9, &hash_builder);
        let entry_c  = EntryWithHash::new(0xCu8, 2, &hash_builder);
        let entry_d  = EntryWithHash::new(0xDu8, 2, &hash_builder);

        let bucket_single_a = Bucket::Single(EntryWithHash::clone(&entry_a));
        let bucket_single_a9 = Bucket::Single(EntryWithHash::clone(&entry_a9));
        let bucket_collision_b_a = Bucket::Collision(
            List::new()
                .push_front(EntryWithHash::clone(&entry_a))
                .push_front(EntryWithHash::clone(&entry_b))
        );
        let bucket_collision_a_b_c = Bucket::Collision(
            List::new()
                .push_front(EntryWithHash::clone(&entry_c))
                .push_front(EntryWithHash::clone(&entry_b))
                .push_front(EntryWithHash::clone(&entry_a))
        );
        let bucket_collision_b9_a_c = Bucket::Collision(
            List::new()
                .push_front(EntryWithHash::clone(&entry_c))
                .push_front(EntryWithHash::clone(&entry_a))
                .push_front(EntryWithHash::clone(&entry_b9))
        );
        let bucket_collision_d_a_b_c = Bucket::Collision(
            List::new()
                .push_front(EntryWithHash::clone(&entry_c))
                .push_front(EntryWithHash::clone(&entry_b))
                .push_front(EntryWithHash::clone(&entry_a))
                .push_front(EntryWithHash::clone(&entry_d))
        );

        // Note that we care about the position of the inserted entry: we want it to be in the
        // beginning of the list as to improve performance with high temporal locality (since
        // `get()` will try to match according to the list order).  The order of the rest of the
        // list must be preserved for the same reason.

        assert_eq!(bucket_single_a.insert(entry_a9.clone()), (bucket_single_a9, false));
        assert_eq!(bucket_single_a.insert(entry_b.clone()), (bucket_collision_b_a, true));

        assert_eq!(bucket_collision_a_b_c.insert(entry_b9.clone()), (bucket_collision_b9_a_c, false));
        assert_eq!(bucket_collision_a_b_c.insert(entry_d.clone()), (bucket_collision_d_a_b_c, true));
    }

    #[test]
    fn test_remove() -> () {
        let hash_builder = RandomState::new();

        let entry_a  = EntryWithHash::new(0xAu8, 0, &hash_builder);
        let entry_b  = EntryWithHash::new(0xBu8, 1, &hash_builder);
        let entry_c  = EntryWithHash::new(0xCu8, 2, &hash_builder);
        let entry_d  = EntryWithHash::new(0xDu8, 2, &hash_builder);

        let bucket_single_a = Bucket::Single(EntryWithHash::clone(&entry_a));
        let bucket_collision_b_c = Bucket::Collision(
            List::new()
                .push_front(EntryWithHash::clone(&entry_c))
                .push_front(EntryWithHash::clone(&entry_b))
        );
        let bucket_collision_a_b_c = Bucket::Collision(
            List::new()
                .push_front(EntryWithHash::clone(&entry_c))
                .push_front(EntryWithHash::clone(&entry_b))
                .push_front(EntryWithHash::clone(&entry_a))
        );

        assert_eq!(bucket_single_a.remove(entry_a.key(), entry_a.key_hash), (None, true));
        assert_eq!(bucket_single_a.remove(entry_b.key(), entry_b.key_hash), (Some(bucket_single_a), false));

        assert_eq!(bucket_collision_a_b_c.remove(entry_a.key(), entry_a.key_hash), (Some(bucket_collision_b_c), true));
        assert_eq!(bucket_collision_a_b_c.remove(entry_d.key(), entry_d.key_hash), (Some(bucket_collision_a_b_c), false));
    }
}

mod hasher_mocks {
    use std::collections::HashMap;
    use std::hash::Hasher;
    use super::*;

    pub struct MockedHashBuilder {
        byte_map: HashMap<u8, HashValue>,
    }

    pub struct MockedHasher {
        last_byte: Option<u8>,
        byte_map:  HashMap<u8, HashValue>,
    }

    impl MockedHashBuilder {
        pub fn new(byte_map: HashMap<u8, HashValue>) -> MockedHashBuilder {
            MockedHashBuilder {
                byte_map
            }
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
            MockedHasher {
                last_byte: None,
                byte_map: self.byte_map.clone(),
            }
        }
    }

    impl Hasher for MockedHasher {
        fn finish(&self) -> HashValue {
            *self.byte_map.get(self.last_byte.as_ref().unwrap()).unwrap()
        }

        fn write(&mut self, bytes: &[u8]) -> () {
            self.last_byte = self.last_byte.or(bytes.last().map(|b| *b));
        }
    }

    pub struct LimitedHashSpaceHashBuilder {
        inner_hash_builder: RandomState,
        hash_space_size: usize,
    }

    pub struct LimitedHashSpaceHasher {
        inner_hasher: ::std::collections::hash_map::DefaultHasher,
        hash_space_size: usize,
    }

    impl LimitedHashSpaceHashBuilder {
        pub fn new(hash_space_size: usize) -> LimitedHashSpaceHashBuilder {
            LimitedHashSpaceHashBuilder {
                inner_hash_builder: RandomState::new(),
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
                inner_hasher: self.inner_hash_builder.build_hasher(),
                hash_space_size: self.hash_space_size,
            }
        }
    }

    impl Hasher for LimitedHashSpaceHasher {
        fn finish(&self) -> HashValue {
            self.inner_hasher.finish() % (self.hash_space_size as HashValue)
        }

        fn write(&mut self, bytes: &[u8]) -> () {
            self.inner_hasher.write(bytes);
        }
    }
}

mod node {
    use super::*;
    use self::hasher_mocks::*;
    use std::collections::HashMap;

    #[test]
    fn test_new_empty_branch() -> () {
        let node: Node<u32, u32> = Node::new_empty_branch();

        match node {
            Node::Branch(array) => assert_eq!(array.size(), 0),
            _ => panic!("Invalid node type"),
        }
    }

    #[test]
    fn test_index_from_hash() -> () {
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
        let hash_mapping: HashMap<u8, HashValue> = [
            (0xA, 0b_0010_0110),
            (0xB, 0b_0001_0110),
            (0xC, 0b_0100_0010),
            (0xD, 0b_0000_1000 | (0b0111 << 60)),
            (0xE, 0b_0000_1000 | (0b0111 << 60)),
            (0x0, 0b_0000_1000 | (0b0111 << 60)),
            (0x1, 0b_0000_0110 | (0b0101 << 60)),
            (0x2, 0b_0000_1111 | (0b0111 << 60)),
        ].iter().cloned().collect();

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
    fn dummy_hash_trie_map() -> HashTrieMap<u8, i32, MockedHashBuilder> {
        let hash_builder: MockedHashBuilder = dummy_hash_builder();

        let entry_a = EntryWithHash::new(0xAu8, 0, &hash_builder);
        let entry_b = EntryWithHash::new(0xBu8, 1, &hash_builder);
        let entry_c = EntryWithHash::new(0xCu8, 2, &hash_builder);
        let entry_d = EntryWithHash::new(0xDu8, 3, &hash_builder);
        let entry_e = EntryWithHash::new(0xEu8, 4, &hash_builder);

        let bucket_a  = Bucket::Single(entry_a);
        let bucket_b  = Bucket::Single(entry_b);
        let bucket_c  = Bucket::Single(entry_c);
        let bucket_de = Bucket::Collision(List::new().push_front(entry_d).push_front(entry_e));

        let node_depth_1_first = Node::Branch(
            SparseArrayUsize::new()
                .set(1, Arc::new(Node::Leaf(bucket_b)))
                .set(2, Arc::new(Node::Leaf(bucket_a)))
        );

        let node_maximum_depth = Node::Branch(
            SparseArrayUsize::new()
                .set(7, Arc::new(Node::Leaf(bucket_de)))
        );

        let maximum_depth_branch = {
            let mut branch = node_maximum_depth;

            for _ in 0..14 {
                branch = Node::Branch(
                    SparseArrayUsize::new()
                        .set(0, Arc::new(branch))
                );
            }

            branch
        };

        let node_root = Node::Branch(
            SparseArrayUsize::new()
                .set(2, Arc::new(Node::Leaf(bucket_c)))
                .set(6, Arc::new(node_depth_1_first))
                .set(8, Arc::new(maximum_depth_branch))
        );

        HashTrieMap {
            root: Arc::new(node_root),
            size: 5,
            degree: 16,
            hasher_builder: hash_builder,
        }
    }

    #[test]
    fn test_get() -> () {
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
    fn test_contains_key() -> () {
        let map = dummy_hash_trie_map();

        assert!(map.contains_key(&0xA));
        assert!(map.contains_key(&0xE));
        assert!(!map.contains_key(&0x0));
    }

    #[test]
    fn test_insert() -> () {
        let mut map =
            HashTrieMap::new_with_hasher_and_degree(dummy_hash_builder(), 16);

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
    fn test_compress() -> () {
        let hash_builder: MockedHashBuilder = dummy_hash_builder();

        let entry_a = EntryWithHash::new(0xAu8, 0, &hash_builder);
        let entry_b = EntryWithHash::new(0xBu8, 1, &hash_builder);

        let bucket_a = Bucket::Single(entry_a.clone());
        let bucket_b = Bucket::Single(entry_b.clone());
        let bucket_a_b = Bucket::Collision(
            List::new().push_front(entry_b.clone()).push_front(entry_a.clone())
        );

        let empty_branch = Node::<u8, i32>::new_empty_branch();
        let branch_with_collision = {
            let array =
                SparseArrayUsize::new()
                    .set(4, Arc::new(Node::Leaf(bucket_a_b.clone())));

            Arc::new(Node::Branch(array))
        };
        let branch_with_two_subtrees = {
            let array =
                SparseArrayUsize::new()
                    .set(4, Arc::new(Node::Leaf(bucket_a.clone())))
                    .set(7, Arc::new(Node::Leaf(bucket_b.clone())));

            Arc::new(Node::Branch(array))
        };
        let branch_with_single_bucket = {
            let array =
                SparseArrayUsize::new()
                    .set(4, Arc::new(Node::Leaf(bucket_a.clone())));

            Node::Branch(array)
        };
        let branch_with_branch= {
            let array =
                SparseArrayUsize::new()
                    .set(4, Arc::new(Node::<u8, i32>::new_empty_branch()));

            Arc::new(Node::Branch(array))
        };
        let leaf_with_single_bucket_a =
            Arc::new(Node::Leaf(bucket_a.clone()));
        let leaf_with_collision_bucket_a_b =
            Arc::new(Node::Leaf(bucket_a_b.clone()));

        assert_eq!(Node::clone(&empty_branch).compress(), None);
        assert_eq!(Node::clone(&branch_with_collision).compress(), Some(branch_with_collision));
        assert_eq!(Node::clone(&branch_with_two_subtrees).compress(), Some(branch_with_two_subtrees));
        assert_eq!(Node::clone(&branch_with_single_bucket).compress(), Some(leaf_with_single_bucket_a.clone()));
        assert_eq!(Node::clone(&branch_with_branch).compress(), Some(branch_with_branch));

        assert_eq!(Node::clone(&leaf_with_single_bucket_a).compress(), Some(leaf_with_single_bucket_a));
        assert_eq!(Node::clone(&leaf_with_collision_bucket_a_b).compress(), Some(leaf_with_collision_bucket_a_b));
    }

    #[test]
    fn test_remove() -> () {
        // This test assumes that `insert()` works correctly.
        let map_a_b_c_d_e =
            HashTrieMap::new_with_hasher_and_degree(dummy_hash_builder(), 16)
                .insert(0xA, 0)
                .insert(0xB, 1)
                .insert(0xC, 2)
                .insert(0xD, 3)
                .insert(0xE, 4);
        let map_a_b_d_e =
            HashTrieMap::new_with_hasher_and_degree(dummy_hash_builder(), 16)
                .insert(0xA, 0)
                .insert(0xB, 1)
                .insert(0xD, 3)
                .insert(0xE, 4);
        let map_a_c_d_e =
            HashTrieMap::new_with_hasher_and_degree(dummy_hash_builder(), 16)
                .insert(0xA, 0)
                .insert(0xC, 2)
                .insert(0xD, 3)
                .insert(0xE, 4);
        let map_c_d_e =
            HashTrieMap::new_with_hasher_and_degree(dummy_hash_builder(), 16)
                .insert(0xC, 2)
                .insert(0xD, 3)
                .insert(0xE, 4);
        let map_a_b_c_e =
            HashTrieMap::new_with_hasher_and_degree(dummy_hash_builder(), 16)
                .insert(0xA, 0)
                .insert(0xB, 1)
                .insert(0xC, 2)
                .insert(0xE, 4);
        let map_a_b_c =
            HashTrieMap::new_with_hasher_and_degree(dummy_hash_builder(), 16)
                .insert(0xA, 0)
                .insert(0xB, 1)
                .insert(0xC, 2);
        let map_empty =
            HashTrieMap::new_with_hasher_and_degree(dummy_hash_builder(), 16);

        // Just a sanity check.
        assert_eq!(map_a_b_c_d_e.root, dummy_hash_trie_map().root);

        let removed_c   = map_a_b_c_d_e.remove(&0xC);
        let removed_b   = map_a_b_c_d_e.remove(&0xB);
        let removed_b_a = map_a_b_c_d_e.remove(&0xB).remove(&0xA);
        let removed_d   = map_a_b_c_d_e.remove(&0xD);
        let removed_d_e = map_a_b_c_d_e.remove(&0xD).remove(&0xE);
        let removed_all = map_a_b_c_d_e
            .remove(&0xA)
            .remove(&0xB)
            .remove(&0xC)
            .remove(&0xD)
            .remove(&0xE);

        assert_eq!(removed_c.root,   map_a_b_d_e.root);
        assert_eq!(removed_b.root,   map_a_c_d_e.root);
        assert_eq!(removed_b_a.root, map_c_d_e.root);
        assert_eq!(removed_d.root,   map_a_b_c_e.root);
        assert_eq!(removed_d_e.root, map_a_b_c.root);
        assert_eq!(removed_all.root, map_empty.root);

        assert_eq!(map_a_b_c_d_e.remove(&0x0).root, map_a_b_c_d_e.root);
        assert_eq!(map_a_b_c_d_e.remove(&0x1).root, map_a_b_c_d_e.root);
        assert_eq!(map_a_b_c_d_e.remove(&0x2).root, map_a_b_c_d_e.root);
    }
}

mod iter {
    use super::*;

    #[test]
    fn test_trie_max_height() -> () {
        assert_eq!(iter_utils::trie_max_height(2), 64);
        assert_eq!(iter_utils::trie_max_height(16), 16);
        assert_eq!(iter_utils::trie_max_height(32), 13);
        assert_eq!(iter_utils::trie_max_height(64), 11);
    }

    #[test]
    fn test_iter_empty() -> () {
        let map: HashTrieMap<i32, i32> = HashTrieMap::new();

        for _ in map.iter() {
            panic!("iterator should be empty");
        }
    }

    fn iterator_test<H: BuildHasher + Clone>(initial_map: HashTrieMap<u32, i32, H>) -> () {
        let mut map = initial_map;
        let limit: usize = 50_000;

        for i in 0..limit {
            map = map.insert(i as u32, -(i as i32));
        }

        let mut touched = vec![false; limit];

        for (k, v) in map.iter() {
            assert!(!touched[*k as usize]);

            assert_eq!(*k as i32, -(*v as i32));

            touched[*k as usize] = true;
        }

        assert!(touched.iter().all(|b| *b));
    }

    #[test]
    fn test_iter() -> () {
        let degrees: Vec<u8> = [2, 4, 16, 32, DEFAULT_DEGREE].iter()
            .map(|d| *d)
            .filter(|d| *d <= DEFAULT_DEGREE) // we only want valid degrees
            .collect();

        for degree in degrees {
            iterator_test(HashTrieMap::new_with_degree(degree));
        }
    }

    #[test]
    fn test_iter_high_collision() -> () {
        let degrees: Vec<u8> = [2, 4, 16, 32, DEFAULT_DEGREE].iter()
            .map(|d| *d)
            .filter(|d| *d <= DEFAULT_DEGREE) // we only want valid degrees
            .collect();

        for degree in degrees {
            let hasher =
                hasher_mocks::LimitedHashSpaceHashBuilder::new(1000);
            iterator_test(HashTrieMap::new_with_hasher_and_degree(hasher, degree));
        }
    }

    #[test]
    fn test_iter_size_hint() -> () {
        let map = HashTrieMap::new()
            .insert(0, 10)
            .insert(1, 11)
            .insert(2, 12);
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
    fn test_iter_keys() -> () {
        let map = HashTrieMap::new()
            .insert(0, 10)
            .insert(1, 11)
            .insert(2, 12);

        let mut touched = vec![false; 3];

        for k in map.keys() {
            assert!(!touched[*k as usize]);
            touched[*k as usize] = true;
        }

        assert!(touched.iter().all(|b| *b));
    }

    #[test]
    fn test_iter_values() -> () {
        let map = HashTrieMap::new()
            .insert(10, 0)
            .insert(11, 1)
            .insert(12, 2);

        let mut touched = vec![false; 3];

        for v in map.values() {
            assert!(!touched[*v as usize]);
            touched[*v as usize] = true;
        }

        assert!(touched.iter().all(|b| *b));
    }

    #[test]
    fn test_into_iterator() -> () {
        let map = HashTrieMap::new()
            .insert(0, 10)
            .insert(1, 11)
            .insert(2, 12);
        let mut left = 3;

        for _ in &map {
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
        let _: Box<Send> = Box::new(HashTrieMap::<i32, i32>::new());
    }

    #[test]
    fn test_is_sync() -> () {
        let _: Box<Sync> = Box::new(HashTrieMap::<i32, i32>::new());
    }
}

#[test]
fn test_macro_ht_map() -> () {
    let set_1 = HashTrieMap::new()
        .insert(1, 2);
    let set_1_2_3 = HashTrieMap::new()
        .insert(1, 2)
        .insert(2, 3)
        .insert(3, 4);

    assert_eq!(HashTrieMap::<u32, u32>::new(), ht_map![]);
    assert_eq!(set_1, ht_map![1 => 2]);
    assert_eq!(set_1_2_3, ht_map![1 => 2, 2 => 3, 3 => 4]);
}

#[test]
fn test_insert_simple() -> () {
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

fn insert_test<H: BuildHasher + Clone>(initial_map: HashTrieMap<u32, i32, H>) -> () {
    let mut map = initial_map;
    let limit = 50_000;
    let overwrite_limit = 10_000;

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
fn test_insert() -> () {
    let degrees: Vec<u8> = [2, 4, 16, 32, DEFAULT_DEGREE].iter()
        .map(|d| *d)
        .filter(|d| *d <= DEFAULT_DEGREE) // we only want valid degrees
        .collect();

    for degree in degrees {
        insert_test(HashTrieMap::new_with_degree(degree));
    }
}

#[test]
fn test_insert_high_collision() -> () {
    let degrees: Vec<u8> = [2, 4, 16, 32, DEFAULT_DEGREE].iter()
        .map(|d| *d)
        .filter(|d| *d <= DEFAULT_DEGREE) // we only want valid degrees
        .collect();

    for degree in degrees {
        let hasher =
            hasher_mocks::LimitedHashSpaceHashBuilder::new(1000);
        insert_test(HashTrieMap::new_with_hasher_and_degree(hasher, degree));
    }
}

#[test]
fn test_remove_simple() -> () {
    let mut map = HashTrieMap::new()
        .insert("foo", 4)
        .insert("bar", 12)
        .insert("mumble", 13)
        .insert("baz", 42);
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

fn remove_test<H: BuildHasher + Clone>(initial_map: HashTrieMap<u32, i32, H>) -> () {
    let mut map = initial_map;
    let limit = 50_000;

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
fn test_remove() -> () {
    let degrees: Vec<u8> = [2, 4, 16, 32, DEFAULT_DEGREE].iter()
        .map(|d| *d)
        .filter(|d| *d <= DEFAULT_DEGREE) // we only want valid degrees
        .collect();

    for degree in degrees {
        remove_test(HashTrieMap::new_with_degree(degree));
    }
}

#[test]
fn test_remove_high_collision() -> () {
    let degrees: Vec<u8> = [2, 4, 16, 32, DEFAULT_DEGREE].iter()
        .map(|d| *d)
        .filter(|d| *d <= DEFAULT_DEGREE) // we only want valid degrees
        .collect();

    for degree in degrees {
        let hasher =
            hasher_mocks::LimitedHashSpaceHashBuilder::new(1000);
        remove_test(HashTrieMap::new_with_hasher_and_degree(hasher, degree));
    }
}

#[test]
fn test_index() -> () {
    let map =
        HashTrieMap::new()
            .insert(5, "hello")
            .insert(12, "there");

    assert_eq!(map[&5], "hello");
    assert_eq!(map[&12], "there");
}

#[test]
fn test_from_iterator() -> () {
    let vec: Vec<(i32, &str)> = vec![(2, "two"), (5, "five")];
    let map: HashTrieMap<i32, &str> = vec.iter().map(|v| *v).collect();
    let expected_map =
        HashTrieMap::new()
            .insert(2, "two")
            .insert(5, "five");

    assert_eq!(map, expected_map);
}

#[test]
fn test_default() -> () {
    let map: HashTrieMap<u32, char> = HashTrieMap::default();

    assert_eq!(map.size(), 0);
    assert!(map.is_empty());
}

#[test]
fn test_display() -> () {
    let empty_map: HashTrieMap<i32, i32> = HashTrieMap::new();
    let singleton_map = HashTrieMap::new()
        .insert("hi", "hello");
    let map = HashTrieMap::new()
        .insert(5, "hello")
        .insert(12, "there");

    assert_eq!(format!("{}", empty_map), "{}");
    assert_eq!(format!("{}", singleton_map), "{hi: hello}");
    assert!(format!("{}", map) == "{5: hello, 12: there}" || format!("{}", map) == "{12: there, 5: hello}");
}

#[test]
fn test_eq() -> () {
    let map_1 = HashTrieMap::new()
        .insert("a", 0xa)
        .insert("b", 0xb);
    let map_1_prime = HashTrieMap::new()
        .insert("a", 0xa)
        .insert("b", 0xb);
    let map_1_prime_2 = HashTrieMap::new()
        .insert("a", 0xa)
        .insert("b", 0xb)
        .insert("b", 0xb);
    let map_2 = HashTrieMap::new()
        .insert("a", 0xa)
        .insert("b", 0xb + 1);
    let map_3 = HashTrieMap::new()
        .insert("a", 0xa)
        .insert("b", 0xb + 1)
        .insert("c", 0xc);

    assert_eq!(map_1, map_1_prime);
    assert_eq!(map_1, map_1_prime_2);
    assert_eq!(map_1, map_1);
    assert_eq!(map_2, map_2);

    // We also check this since `assert_ne!()` does not call `ne`.
    assert!(map_1.ne(&map_2));
    assert!(map_2.ne(&map_3));
}

#[test]
fn test_clone() -> () {
    let map =
        HashTrieMap::new()
            .insert("hello", 4)
            .insert("there", 5);
    let clone = map.clone();

    assert_eq!(clone.size(), map.size());
    assert_eq!(clone.get("hello"), Some(&4));
    assert_eq!(clone.get("there"), Some(&5));
}

#[cfg(feature = "serde")]
#[test]
fn test_serde() -> () {
    use bincode::{serialize, deserialize};
    let hashtriemap: HashTrieMap<i32, i32> = HashTrieMap::from_iter(vec![(5,6),(7,8),(9,10),(11,12)].into_iter());
    let encoded = serialize(&hashtriemap).unwrap();
    let decoded: HashTrieMap<i32, i32> = deserialize(&encoded).unwrap();
    assert_eq!(hashtriemap, decoded);
}
