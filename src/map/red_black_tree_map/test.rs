/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

extern crate rand;

use super::*;
// use std::fmt::Display;

#[derive(Debug)]
enum InvariantViolation {
    SizeConsistency,
    BinarySearch,
    BlackRoot,
    RedNodeBlackChildren,
    BlackHeightBalanced,
}

impl<K, V> Node<K, V> {
    fn new_black(entry: Entry<K, V>) -> Node<K, V> {
        Node {
            entry: Arc::new(entry),
            color: Color::Black,
            left:  None,
            right: None,
        }
    }

    fn count(&self) -> usize {
        1 + self.left.as_ref().map_or(0, |l| l.count())
            + self.right.as_ref().map_or(0, |r| r.count())
    }

    fn is_black_height_balanced(&self) -> bool {
        fn black_height<K, V>(node: &Node<K, V>) -> Result<usize, ()> {
            let bheight_left  = node.left.as_ref().map_or(Ok(0),  |l| black_height(l))?;
            let bheight_right = node.right.as_ref().map_or(Ok(0), |r| black_height(r))?;

            if bheight_left == bheight_right {
                let bheight = bheight_right;
                Ok(bheight + if node.color == Color::Black { 1 } else { 0 })
            } else {
                Err(())
            }
        }

        black_height(self).is_ok()
    }

    fn red_nodes_have_black_children(&self) -> bool {
        let self_ok = if self.color == Color::Red {
            self.left.as_ref().map_or(Color::Black, |l| l.color) == Color::Black
                && self.right.as_ref().map_or(Color::Black, |r| r.color) == Color::Black
        } else {
            true
        };

        self_ok
            && self.left.as_ref().map_or(true,  |l| l.red_nodes_have_black_children())
            && self.right.as_ref().map_or(true, |r| r.red_nodes_have_black_children())
    }

    fn has_binary_search_property(&self) -> bool
        where K: Clone + Ord {
        fn go<K: Clone + Ord, V>(node: &Node<K, V>, last: &mut Option<K>) -> bool {
            let ok_left = node.left.as_ref().map_or(true, |l| go(l, last));

            let new_last = node.entry.key.clone();

            let ok_node = last.as_ref().map_or(true, |l| *l < new_last);

            *last = Some(new_last);

            let ok_right = node.right.as_ref().map_or(true, |r| go(r, last));

            ok_left && ok_node && ok_right
        }

        let mut last: Option<K> = None;

        go(self, &mut last)
    }
}

impl<K, V> RedBlackTreeMap<K, V>
    where K: Ord + Clone {
    fn check_consistent(&self) -> Result<(), InvariantViolation> {
        if !self.root.as_ref().map_or(true, |r| r.has_binary_search_property()) {
            Result::Err(InvariantViolation::BinarySearch)
        } else if !self.root.as_ref().map_or(true, |r| r.red_nodes_have_black_children()) {
            Result::Err(InvariantViolation::RedNodeBlackChildren)
        } else if !self.root.as_ref().map_or(true, |r| r.is_black_height_balanced()) {
            Result::Err(InvariantViolation::BlackHeightBalanced)
        } else if !self.root.as_ref().map_or(true, |r| r.color == Color::Black) {
            Result::Err(InvariantViolation::BlackRoot)
        } else if self.root.as_ref().map_or(0, |r| r.count()) != self.size() {
            Result::Err(InvariantViolation::SizeConsistency)
        } else {
            Ok(())
        }
    }
}

mod node {
    use super::*;

    fn dummy_entry(v: i32) -> Entry<i32, i32> {
        Entry { key: v, value: v }
    }

    fn dummy_leaf(v: i32) -> Node<i32, i32> {
        Node {
            entry: Arc::new(dummy_entry(v)),
            color: Color::Red,
            left:  None,
            right: None,
        }
    }

    fn dummy_leaf_with_children(
        v: i32,
        left: Option<Node<i32, i32>>,
        right: Option<Node<i32, i32>>
    ) -> Node<i32, i32> {
        Node {
            entry: Arc::new(dummy_entry(v)),
            color: Color::Red,
            left:  left.map(|n| Arc::new(n)),
            right: right.map(|n| Arc::new(n)),
        }
    }

    /// Returns the following tree:
    ///
    /// ```text
    ///           ╭───╮
    ///           │ 1 │
    ///           ╰───╯
    ///           ╱   ╲
    ///          ╱     ╲
    ///      ╭───╮     ╭───╮
    ///      │ 0 │     │ 2 │
    ///      ╰───╯     ╰───╯
    ///                    ╲
    ///                     ╲
    ///                     ╭───╮
    ///                     │ 3 │
    ///                     ╰───╯
    /// ```
    fn dummy_tree_0_1_2_3() -> Node<i32, i32> {
        let node_0 = dummy_leaf(0);
        let node_3 = dummy_leaf(3);
        let node_2 = dummy_leaf_with_children(2, None, Some(node_3));
        let node_1 = dummy_leaf_with_children(1, Some(node_0), Some(node_2));

        node_1
    }

    #[test]
    fn test_get() -> () {
        let tree = dummy_tree_0_1_2_3();

        assert_eq!(tree.get(&0).unwrap().key, 0);
        assert_eq!(tree.get(&1).unwrap().key, 1);
        assert_eq!(tree.get(&2).unwrap().key, 2);
        assert_eq!(tree.get(&3).unwrap().key, 3);
        assert_eq!(tree.get(&4), None);
    }

    #[test]
    fn test_first() -> () {
        let tree = dummy_tree_0_1_2_3();

        assert_eq!(tree.first().key, 0);
    }

    #[test]
    fn test_last() -> () {
        let tree = dummy_tree_0_1_2_3();

        assert_eq!(tree.last().key, 3);
    }

    #[test]
    fn test_balance() -> () {
        //                                                                ╭────────────────────╮
        //                                                                │  ┌───┐             │
        //                                                                │  │   │ Red node    │
        //                                                                │  └───┘             │
        //            ┏━━━┓                                               │                    │
        //            ┃ z ┃                                               │  ┏━━━┓             │
        //            ┗━━━┛                                               │  ┃   ┃ Black node  │
        //             ╱ ╲                                                │  ┗━━━┛             │
        //        ┌───┐   d                                               ╰────────────────────╯
        //        │ y │                      Case 1
        //        └───┘           ╭──────────────────────────────────────────────────╮
        //         ╱ ╲            ╰────────────────────────────────────────────────╮ │
        //     ┌───┐  c                                                            │ │
        //     │ x │                                                               │ │
        //     └───┘                                                               │ │
        //      ╱ ╲                                                                │ │
        //     a   b                                                               │ │
        //                                                                         │ │
        //                                                                         │ │
        //                                                                         │ │
        //            ┏━━━┓                                                        │ │
        //            ┃ z ┃                                                        │ │
        //            ┗━━━┛                                                        │ │
        //             ╱ ╲                                                         │ │
        //        ┌───┐   d                  Case 2                                │ │
        //        │ x │           ╭─────────────────────────────╲                  │ │
        //        └───┘           ╰────────────────────────────╲ ╲                 ╲ ╱
        //         ╱ ╲                                          ╲ ╲
        //        a  ┌───┐                                       ╲ ╲
        //           │ y │                                        ╲ ╲             ┌───┐
        //           └───┘                                         ╲ ╲            │ y │
        //            ╱ ╲                                           ╲  ┃          └───┘
        //           b   c                                          ───┘           ╱ ╲
        //                                                                        ╱   ╲
        //                                                                   ┏━━━┓     ┏━━━┓
        //                                                                   ┃ x ┃     ┃ z ┃
        //            ┏━━━┓                                                  ┗━━━┛     ┗━━━┛
        //            ┃ x ┃                                         ───┐      ╱ ╲       ╱ ╲
        //            ┗━━━┛                                         ╱  ┃     ╱   ╲     ╱   ╲
        //             ╱ ╲                                         ╱ ╱      a     b   c     d
        //            a  ┌───┐                                    ╱ ╱
        //               │ z │                                   ╱ ╱
        //               └───┘               Case 3             ╱ ╱                ╱ ╲
        //                ╱ ╲     ╭────────────────────────────╱ ╱                 │ │
        //            ┌───┐  d    ╰─────────────────────────────╱                  │ │
        //            │ y │                                                        │ │
        //            └───┘                                                        │ │
        //             ╱ ╲                                                         │ │
        //            b   c                                                        │ │
        //                                                                         │ │
        //                                                                         │ │
        //                                                                         │ │
        //            ┏━━━┓                                                        │ │
        //            ┃ x ┃                                                        │ │
        //            ┗━━━┛                                                        │ │
        //             ╱ ╲                                                         │ │
        //            a  ┌───┐               Case 4                                │ │
        //               │ y │    ╭────────────────────────────────────────────────┘ │
        //               └───┘    ╰──────────────────────────────────────────────────┘
        //                ╱ ╲
        //               b  ┌───┐
        //                  │ z │
        //                  └───┘
        //                   ╱ ╲
        //                  c   d

        let entry_x = Arc::new(Entry::new('x', ()));
        let entry_y = Arc::new(Entry::new('y', ()));
        let entry_z = Arc::new(Entry::new('z', ()));

        let tree_a = Arc::new(Node::new_black(Entry::new('a', ())));
        let tree_b = Arc::new(Node::new_black(Entry::new('b', ())));
        let tree_c = Arc::new(Node::new_black(Entry::new('c', ())));
        let tree_d = Arc::new(Node::new_black(Entry::new('d', ())));

        let tree_case_1 = Node {
            entry: Arc::clone(&entry_z),
            color: Color::Black,
            left: Some(Arc::new(Node {
                entry: Arc::clone(&entry_y),
                color: Color::Red,
                left: Some(Arc::new(Node {
                    entry: Arc::clone(&entry_x),
                    color: Color::Red,
                    left:  Some(Arc::clone(&tree_a)),
                    right: Some(Arc::clone(&tree_b)),
                })),
                right: Some(Arc::clone(&tree_c)),
            })),
            right: Some(Arc::clone(&tree_d)),
        };

        let tree_case_2 = Node {
            entry: Arc::clone(&entry_z),
            color: Color::Black,
            left: Some(Arc::new(Node {
                entry: Arc::clone(&entry_x),
                color: Color::Red,
                left: Some(Arc::clone(&tree_a)),
                right: Some(Arc::new(Node {
                    entry: Arc::clone(&entry_y),
                    color: Color::Red,
                    left:  Some(Arc::clone(&tree_b)),
                    right: Some(Arc::clone(&tree_c)),
                })),
            })),
            right: Some(Arc::clone(&tree_d)),
        };

        let tree_case_3 = Node {
            entry: Arc::clone(&entry_x),
            color: Color::Black,
            left:  Some(Arc::clone(&tree_a)),
            right: Some(Arc::new(Node {
                entry: Arc::clone(&entry_z),
                color: Color::Red,
                left:  Some(Arc::new(Node {
                    entry: Arc::clone(&entry_y),
                    color: Color::Red,
                    left:  Some(Arc::clone(&tree_b)),
                    right: Some(Arc::clone(&tree_c)),
                })),
                right: Some(Arc::clone(&tree_d)),
            })),
        };

        let tree_case_4 = Node {
            entry: Arc::clone(&entry_x),
            color: Color::Black,
            left:  Some(Arc::clone(&tree_a)),
            right: Some(Arc::new(Node {
                entry: Arc::clone(&entry_y),
                color: Color::Red,
                left:  Some(Arc::clone(&tree_b)),
                right: Some(Arc::new(Node {
                    entry: Arc::clone(&entry_z),
                    color: Color::Red,
                    left:  Some(Arc::clone(&tree_c)),
                    right: Some(Arc::clone(&tree_d)),
                })),
            })),
        };

        let tree_none_of_the_above = Node {
            entry: Arc::clone(&entry_z),
            color: Color::Black,
            left: Some(Arc::new(Node {
                entry: Arc::clone(&entry_y),
                color: Color::Red,
                left: Some(Arc::new(Node {
                    entry: Arc::clone(&entry_x),
                    color: Color::Black,
                    left:  Some(Arc::clone(&tree_a)),
                    right: Some(Arc::clone(&tree_b)),
                })),
                right: Some(Arc::clone(&tree_c)),
            })),
            right: Some(Arc::clone(&tree_d)),
        };

        let tree_balanced = Node {
            entry: Arc::clone(&entry_y),
            color: Color::Red,
            left: Some(Arc::new(Node {
                entry: Arc::clone(&entry_x),
                color: Color::Black,
                left:  Some(Arc::clone(&tree_a)),
                right: Some(Arc::clone(&tree_b)),
            })),
            right: Some(Arc::new(Node {
                entry: Arc::clone(&entry_z),
                color: Color::Black,
                left:  Some(Arc::clone(&tree_c)),
                right: Some(Arc::clone(&tree_d)),
            })),
        };

        assert_eq!(tree_case_1.clone().balance(), tree_balanced.clone());
        assert_eq!(tree_case_2.clone().balance(), tree_balanced.clone());
        assert_eq!(tree_case_3.clone().balance(), tree_balanced.clone());
        assert_eq!(tree_case_4.clone().balance(), tree_balanced.clone());
        assert_eq!(tree_none_of_the_above.clone().balance(), tree_none_of_the_above.clone());
        assert_eq!(tree_balanced.clone().balance(), tree_balanced.clone());
    }

    #[test]
    fn test_insert() -> () {
        let (node, is_new_key) = Node::insert(None, 0, 1);
        let expected_node = Node::new_black(Entry::new(0, 1));

        assert!(is_new_key);
        assert_eq!(node, expected_node);

        let (node, is_new_key) = Node::insert(Some(&node), 0, 2);
        let expected_node = Node::new_black(Entry::new(0, 2));

        assert!(!is_new_key);
        assert_eq!(node, expected_node);

        let (node, is_new_key) = Node::insert(Some(&node), 10, 3);
        let expected_node = Node {
            entry: Arc::new(Entry::new(0, 2)),
            color: Color::Black,
            left:  None,
            right: Some(Arc::new(Node {
                entry: Arc::new(Entry::new(10, 3)),
                color: Color::Red,
                left:  None,
                right: None,
            })),
        };

        assert!(is_new_key);
        assert_eq!(node, expected_node);

        let (node, is_new_key) = Node::insert(Some(&node), 10, 4);
        let expected_node = Node {
            entry: Arc::new(Entry::new(0, 2)),
            color: Color::Black,
            left:  None,
            right: Some(Arc::new(Node {
                entry: Arc::new(Entry::new(10, 4)),
                color: Color::Red,
                left:  None,
                right: None,
            })),
        };

        assert!(!is_new_key);
        assert_eq!(node, expected_node);

        let (node, is_new_key) = Node::insert(Some(&node), 5, 5);
        // It is going to get rebalanced (by case 3).
        let expected_node = Node {
            entry: Arc::new(Entry::new(5, 5)),
            color: Color::Black,
            left:  Some(Arc::new(Node {
                entry: Arc::new(Entry::new(0, 2)),
                color: Color::Black,
                left:  None,
                right: None,
            })),
            right: Some(Arc::new(Node {
                entry: Arc::new(Entry::new(10, 4)),
                color: Color::Black,
                left:  None,
                right: None,
            })),
        };

        assert!(is_new_key);
        assert_eq!(node, expected_node);

        let (node, is_new_key) = Node::insert(Some(&node), 0, 1);
        // It is going to get rebalanced (by case 3).
        let expected_node = Node {
            entry: Arc::new(Entry::new(5, 5)),
            color: Color::Black,
            left:  Some(Arc::new(Node {
                entry: Arc::new(Entry::new(0, 1)),
                color: Color::Black,
                left:  None,
                right: None,
            })),
            right: Some(Arc::new(Node {
                entry: Arc::new(Entry::new(10, 4)),
                color: Color::Black,
                left:  None,
                right: None,
            })),
        };

        assert!(!is_new_key);
        assert_eq!(node, expected_node);
    }
}

mod internal {
    use super::*;

    fn insert_test(values: &[u32]) -> () {
        let mut map = RedBlackTreeMap::new();

        for (i, &v) in values.iter().enumerate() {
            map = map.insert(v, 2*v);

            if let Err(error) = map.check_consistent() {
                panic!(format!("Consistency error in red-black tree ({:?}).  Insertions: {:?}",
                               error, &values[0..(i + 1)]));
            }

            let other_v = values[i/2];

            assert_eq!(map.get(&v), Some(&(2*v)));
            assert_eq!(map.get(&other_v), Some(&(2*other_v)));
        }
    }

    #[test]
    fn test_insert_sorted() {
        let vec: Vec<u32> = (0..4092).collect();
        insert_test(&vec);
    }

    #[test]
    fn test_insert() {
        use self::rand::Rng;
        use self::rand::SeedableRng;

        let limit = 50_000;
        let seed: [u32; 4] = [24573, 23355, 3457, 25346746];
        let mut rng = rand::ChaChaRng::from_seed(&seed);
        let mut permutation: [u32; 64] = {
            let mut p: [u32; 64] = [0; 64];

            for i in 0..64 {
                p[i as usize] = i;
            }

            p
        };

        for _ in 0..limit {
            rng.shuffle(&mut permutation);

            insert_test(&permutation);
        }
    }

    fn remove_test(values_insert: &[u32], values_remove: &[u32]) -> () {
        let mut map = RedBlackTreeMap::new();

        for &v in values_insert.iter() {
            map = map.insert(v, 2*v);
        }

        for (i, v) in values_remove.iter().enumerate() {
            map = map.remove(v);

            if let Err(error) = map.check_consistent() {
                panic!(format!("Consistency error in red-black tree ({:?}).  Insertions: {:?}.  Removals: {:?}",
                               error, &values_insert, &values_remove[0..(i + 1)]));
            }

            assert!(!map.contains_key(v));
        }
    }

    #[test]
    fn test_remove_sorted() {
        let vec: Vec<u32> = (0..4092).collect();
        let vec_rev: Vec<u32> = (0..4092).rev().collect();
        remove_test(&vec, &vec);
        remove_test(&vec, &vec_rev);
    }

    #[test]
    fn test_remove() {
        use self::rand::Rng;
        use self::rand::SeedableRng;

        let limit = 50_000;
        let seed: [u32; 4] = [24573, 23355, 3457, 25346746];
        let mut rng = rand::ChaChaRng::from_seed(&seed);
        let mut permutation_insert: [u32; 64] = {
            let mut p: [u32; 64] = [0; 64];

            for i in 0..64 {
                p[i as usize] = i;
            }

            p
        };
        let mut permutation_remove: [u32; 64] = permutation_insert;

        for _ in 0..limit {
            rng.shuffle(&mut permutation_insert);
            rng.shuffle(&mut permutation_remove);

            remove_test(&permutation_insert, &permutation_remove);
        }
    }
}

mod iter {
    use super::*;

    #[test]
    fn test_lg_floor() -> () {
        assert_eq!(iter_utils::lg_floor( 1), 0);
        assert_eq!(iter_utils::lg_floor( 2), 1);
        assert_eq!(iter_utils::lg_floor( 3), 1);
        assert_eq!(iter_utils::lg_floor( 4), 2);
        assert_eq!(iter_utils::lg_floor( 5), 2);
        assert_eq!(iter_utils::lg_floor( 7), 2);
        assert_eq!(iter_utils::lg_floor( 8), 3);
        assert_eq!(iter_utils::lg_floor( 9), 3);
        assert_eq!(iter_utils::lg_floor(15), 3);
        assert_eq!(iter_utils::lg_floor(16), 4);
        assert_eq!(iter_utils::lg_floor(17), 4);
    }

    #[test]
    fn test_iter_empty() -> () {
        let map: RedBlackTreeMap<i32, i32> = RedBlackTreeMap::new();

        for _ in map.iter() {
            panic!("iterator should be empty");
        }
    }

    #[test]
    fn test_iter_empty_backwards() -> () {
        let map: RedBlackTreeMap<i32, i32> = RedBlackTreeMap::new();

        for _ in map.iter().rev() {
            panic!("iterator should be empty");
        }
    }

    #[test]
    fn test_iter_big_map() -> () {
        let limit = 512;
        let mut map = RedBlackTreeMap::new();
        let mut expected = 0;
        let mut left = limit;

        for i in (0..limit).rev() {
            map = map.insert(i, 2 * i);
        }

        for (k, v) in map.iter() {
            left -= 1;

            assert!(left >= 0);
            assert_eq!(*k, expected);
            assert_eq!(*v, 2 * expected);

            expected += 1;
        }

        assert_eq!(left, 0);
    }

    #[test]
    fn test_iter_big_map_backwards() -> () {
        let limit = 512;
        let mut map = RedBlackTreeMap::new();
        let mut expected = limit - 1;
        let mut left = limit;

        for i in 0..limit {
            map = map.insert(i, 2 * i);
        }

        for (k, v) in map.iter().rev() {
            left -= 1;

            assert!(left >= 0);
            assert_eq!(*k, expected);
            assert_eq!(*v, 2 * expected);

            expected -= 1;
        }

        assert_eq!(left, 0);
    }

    #[test]
    fn test_iter_both_directions() -> () {
        let map = RedBlackTreeMap::new()
            .insert(0, 10)
            .insert(1, 11)
            .insert(2, 12)
            .insert(3, 13)
            .insert(4, 14)
            .insert(5, 15);
        let mut iterator = map.iter();

        assert_eq!(iterator.next(),      Some((&0, &10)));
        assert_eq!(iterator.next_back(), Some((&5, &15)));
        assert_eq!(iterator.next_back(), Some((&4, &14)));
        assert_eq!(iterator.next(),      Some((&1, &11)));
        assert_eq!(iterator.next(),      Some((&2, &12)));
        assert_eq!(iterator.next_back(), Some((&3, &13)));
        assert_eq!(iterator.next_back(), None);
        assert_eq!(iterator.next(),      None);
    }

    #[test]
    fn test_iter_size_hint() -> () {
        let map = RedBlackTreeMap::new()
            .insert(0, 10)
            .insert(1, 11)
            .insert(2, 12);
        let mut iterator = map.iter();

        assert_eq!(iterator.size_hint(), (3, Some(3)));

        iterator.next();

        assert_eq!(iterator.size_hint(), (2, Some(2)));

        iterator.next_back();

        assert_eq!(iterator.size_hint(), (1, Some(1)));

        iterator.next_back();

        assert_eq!(iterator.size_hint(), (0, Some(0)));
    }

    #[test]
    fn test_iter_keys() -> () {
        let map = RedBlackTreeMap::new()
            .insert(0, 10)
            .insert(1, 11)
            .insert(2, 12);
        let mut iter = map.keys();

        assert_eq!(iter.next(), Some(&0));
        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.next(), Some(&2));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_iter_values() -> () {
        let map = RedBlackTreeMap::new()
            .insert(10, 0)
            .insert(11, 1)
            .insert(12, 2);
        let mut iter = map.values();

        assert_eq!(iter.next(), Some(&0));
        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.next(), Some(&2));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_into_iterator() -> () {
        let map = RedBlackTreeMap::new()
            .insert(0, 0)
            .insert(1, 2)
            .insert(2, 4)
            .insert(3, 6);
        let mut expected = 0;
        let mut left = 4;

        for (k, v) in &map {
            left -= 1;

            assert!(left >= 0);
            assert_eq!(*k, expected);
            assert_eq!(*v, 2 * expected);

            expected += 1;
        }

        assert_eq!(left, 0);
    }
}

mod compile_time {
    use super::*;

    #[test]
    fn test_is_send() -> () {
        let _: Box<Send> = Box::new(RedBlackTreeMap::<i32, i32>::new());
    }

    #[test]
    fn test_is_sync() -> () {
        let _: Box<Sync> = Box::new(RedBlackTreeMap::<i32, i32>::new());
    }
}

#[test]
fn test_insert_simple() -> () {
    let mut map = RedBlackTreeMap::new();
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

    assert!(map.contains_key("baz"));
}

#[test]
fn test_insert() -> () {
    let mut map = RedBlackTreeMap::new();
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
fn test_contains_key() -> () {
    let map = RedBlackTreeMap::new().insert("foo", 7);

    assert!(map.contains_key("foo"));
    assert!(!map.contains_key("baz"));
}

#[test]
fn test_remove_simple() -> () {
    let mut map = RedBlackTreeMap::new()
        .insert("foo", 4)
        .insert("bar", 12)
        .insert("mumble", 13)
        .insert("baz", 42);
    let empty_map: RedBlackTreeMap<i32, i32> = RedBlackTreeMap::new();

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

#[test]
fn test_remove() -> () {
    let mut map = RedBlackTreeMap::new();
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
fn test_first() -> () {
    let map =
        RedBlackTreeMap::new()
            .insert(5, "hello")
            .insert(12, "there");

    assert_eq!(map.first(), Some((&5, &"hello")));
}

#[test]
fn test_last() -> () {
    let map =
        RedBlackTreeMap::new()
            .insert(5, "hello")
            .insert(12, "there");

    assert_eq!(map.last(), Some((&12, &"there")));
}

#[test]
fn test_index() -> () {
    let map =
        RedBlackTreeMap::new()
            .insert(5, "hello")
            .insert(12, "there");

    assert_eq!(map[&5], "hello");
    assert_eq!(map[&12], "there");
}

#[test]
fn test_from_iterator() -> () {
    let vec: Vec<(i32, &str)> = vec![(2, "two"), (5, "five")];
    let map: RedBlackTreeMap<i32, &str> = vec.iter().map(|v| *v).collect();
    let expected_map =
        RedBlackTreeMap::new()
            .insert(2, "two")
            .insert(5, "five");

    assert_eq!(map, expected_map);
}

#[test]
fn test_default() -> () {
    let map: RedBlackTreeMap<u32, char> = RedBlackTreeMap::default();

    assert_eq!(map.size(), 0);
    assert!(map.is_empty());
}

#[test]
fn test_display() -> () {
    let empty_map: RedBlackTreeMap<i32, i32> = RedBlackTreeMap::new();
    let singleton_map = RedBlackTreeMap::new()
        .insert("hi", "hello");
    let map = RedBlackTreeMap::new()
        .insert(5, "hello")
        .insert(12, "there");

    assert_eq!(format!("{}", empty_map), "{}");
    assert_eq!(format!("{}", singleton_map), "{hi: hello}");
    assert_eq!(format!("{}", map), "{5: hello, 12: there}");
}

#[test]
fn test_eq() -> () {
    let map_1 = RedBlackTreeMap::new()
        .insert("a", 0xa)
        .insert("b", 0xb);
    let map_1_prime = RedBlackTreeMap::new()
        .insert("a", 0xa)
        .insert("b", 0xb);
    let map_1_prime_2 = RedBlackTreeMap::new()
        .insert("a", 0xa)
        .insert("b", 0xb)
        .insert("b", 0xb);
    let map_2 = RedBlackTreeMap::new()
        .insert("a", 0xa)
        .insert("b", 0xb + 1);
    let map_3 = RedBlackTreeMap::new()
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
fn test_partial_ord() -> () {
    let map_1 = RedBlackTreeMap::new()
        .insert("a", 0xa);
    let map_1_prime = RedBlackTreeMap::new()
        .insert("a", 0xa);
    let map_2 = RedBlackTreeMap::new()
        .insert("b", 0xb);
    let map_3 = RedBlackTreeMap::new()
        .insert(0, 0.0);
    let map_4 = RedBlackTreeMap::new()
        .insert(0, ::std::f32::NAN);

    assert_eq!(map_1.partial_cmp(&map_1_prime), Some(Ordering::Equal));
    assert_eq!(map_1.partial_cmp(&map_2), Some(Ordering::Less));
    assert_eq!(map_2.partial_cmp(&map_1), Some(Ordering::Greater));
    assert_eq!(map_3.partial_cmp(&map_4), None);
}

#[test]
fn test_ord() -> () {
    let map_1 = RedBlackTreeMap::new()
        .insert("a", 0xa);
    let map_1_prime = RedBlackTreeMap::new()
        .insert("a", 0xa);
    let map_2 = RedBlackTreeMap::new()
        .insert("b", 0xb);

    assert_eq!(map_1.cmp(&map_1_prime), Ordering::Equal);
    assert_eq!(map_1.cmp(&map_2), Ordering::Less);
    assert_eq!(map_2.cmp(&map_1), Ordering::Greater);
}

fn hash<K: Ord + Hash, V: Hash>(map: &RedBlackTreeMap<K, V>) -> u64 {
    let mut hasher = ::std::collections::hash_map::DefaultHasher::new();

    map.hash(&mut hasher);

    hasher.finish()
}

#[test]
fn test_hash() -> () {
    let map_1 = RedBlackTreeMap::new()
        .insert("a", 0xa);
    let map_1_prime = RedBlackTreeMap::new()
        .insert("a", 0xa);
    let map_2 = RedBlackTreeMap::new()
        .insert("b", 0xb)
        .insert("a", 0xa);

    assert_eq!(hash(&map_1), hash(&map_1));
    assert_eq!(hash(&map_1), hash(&map_1_prime));
    assert_ne!(hash(&map_1), hash(&map_2));
}

#[test]
fn test_clone() -> () {
    let map =
        RedBlackTreeMap::new()
            .insert("hello", 4)
            .insert("there", 5);
    let clone = map.clone();

    assert_eq!(clone.size(), map.size());
    assert_eq!(clone.get("hello"), Some(&4));
    assert_eq!(clone.get("there"), Some(&5));
}

#[cfg(feature = "serde")]
#[test]
fn test_serde() {
    use bincode::{serialize, deserialize, Bounded};
    let rbtreemap: RedBlackTreeMap<i32, i32> = RedBlackTreeMap::from_iter(vec![(5,6),(7,8),(9,10),(11,12)].into_iter());
    let encoded = serialize(&rbtreemap, Bounded(100)).unwrap();
    let decoded: RedBlackTreeMap<i32, i32> = deserialize(&encoded).unwrap();
    assert_eq!(rbtreemap, decoded);
}
