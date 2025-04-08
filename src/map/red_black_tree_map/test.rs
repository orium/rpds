/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

#![allow(clippy::cast_possible_truncation)]
#![allow(clippy::cast_possible_wrap)]
#![allow(clippy::cast_sign_loss)]

use super::*;
use alloc::vec::Vec;
use pretty_assertions::assert_eq;
use static_assertions::assert_impl_all;

assert_impl_all!(RedBlackTreeMapSync<i32, i32>: Send, Sync);

#[allow(dead_code)]
fn compile_time_macro_red_black_tree_map_sync_is_send_and_sync() -> impl Send + Sync {
    rbt_map_sync!(0 => 0)
}

#[derive(Debug)]
enum InvariantViolation {
    SizeConsistency,
    BinarySearch,
    BlackRoot,
    RedNodeBlackChildren,
    BlackHeightBalanced,
}

impl<K, V, P> Node<K, V, P>
where
    P: SharedPointerKind,
{
    fn count(&self) -> usize {
        1 + self.left.as_ref().map_or(0, |l| l.count())
            + self.right.as_ref().map_or(0, |r| r.count())
    }

    fn is_black_height_balanced(&self) -> bool {
        fn black_height<K, V, P: SharedPointerKind>(node: &Node<K, V, P>) -> Result<usize, ()> {
            let bheight_left = node.left.as_ref().map_or(Ok(0), |l| black_height(l))?;
            let bheight_right = node.right.as_ref().map_or(Ok(0), |r| black_height(r))?;

            if bheight_left == bheight_right {
                let bheight = bheight_right;
                Ok(bheight + usize::from(node.color == Color::Black))
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
            && self.left.as_ref().is_none_or(|l| l.red_nodes_have_black_children())
            && self.right.as_ref().is_none_or(|r| r.red_nodes_have_black_children())
    }

    fn has_binary_search_property(&self) -> bool
    where
        K: Clone + Ord,
    {
        fn go<K: Clone + Ord, V, P: SharedPointerKind>(
            node: &Node<K, V, P>,
            last: &mut Option<K>,
        ) -> bool {
            let ok_left = node.left.as_ref().is_none_or(|l| go(l, last));

            let new_last = node.entry.key.clone();

            let ok_node = last.as_ref().is_none_or(|l| *l < new_last);

            *last = Some(new_last);

            let ok_right = node.right.as_ref().is_none_or(|r| go(r, last));

            ok_left && ok_node && ok_right
        }

        let mut last: Option<K> = None;

        go(self, &mut last)
    }

    fn make_black(self) -> Node<K, V, P> {
        let mut node = self;
        node.color = Color::Black;
        node
    }

    fn make_red(self) -> Node<K, V, P> {
        let mut node = self;
        node.color = Color::Red;
        node
    }
}

impl<K, V> RedBlackTreeMap<K, V>
where
    K: Ord + Clone,
{
    fn check_consistent(&self) -> Result<(), InvariantViolation> {
        if !self.root.as_ref().is_none_or(|r| r.has_binary_search_property()) {
            Err(InvariantViolation::BinarySearch)
        } else if !self.root.as_ref().is_none_or(|r| r.red_nodes_have_black_children()) {
            Err(InvariantViolation::RedNodeBlackChildren)
        } else if !self.root.as_ref().is_none_or(|r| r.is_black_height_balanced()) {
            Err(InvariantViolation::BlackHeightBalanced)
        } else if !self.root.as_ref().is_none_or(|r| r.color == Color::Black) {
            Err(InvariantViolation::BlackRoot)
        } else if self.root.as_ref().map_or(0, |r| r.count()) != self.size() {
            Err(InvariantViolation::SizeConsistency)
        } else {
            Ok(())
        }
    }
}

impl<K, V, P> PartialEq for Node<K, V, P>
where
    K: PartialEq,
    V: PartialEq,
    P: SharedPointerKind,
{
    fn eq(&self, other: &Node<K, V, P>) -> bool {
        self.entry == other.entry
            && self.color == other.color
            && self.left == other.left
            && self.right == other.right
    }
}

impl<K: Eq, V: Eq, P> Eq for Node<K, V, P> where P: SharedPointerKind {}

mod node {
    use super::*;
    use pretty_assertions::assert_eq;

    fn dummy_entry<T: Clone>(v: T) -> Entry<T, T> {
        Entry { key: v.clone(), value: v }
    }

    fn dummy_node<T: Clone>(v: T) -> Node<T, T, RcK> {
        Node {
            entry: SharedPointer::new(dummy_entry(v)),
            color: Color::Red,
            left: None,
            right: None,
        }
    }

    fn dummy_node_with_children<T: Clone>(
        v: T,
        left: Option<Node<T, T, RcK>>,
        right: Option<Node<T, T, RcK>>,
    ) -> Node<T, T, RcK> {
        Node {
            entry: SharedPointer::new(dummy_entry(v)),
            color: Color::Red,
            left: left.map(SharedPointer::new),
            right: right.map(SharedPointer::new),
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
    fn dummy_tree_0_1_2_3() -> Node<i32, i32, RcK> {
        let node_0 = dummy_node(0);
        let node_3 = dummy_node(3);
        let node_2 = dummy_node_with_children(2, None, Some(node_3));

        dummy_node_with_children(1, Some(node_0), Some(node_2))
    }

    #[test]
    fn test_get() {
        let tree = dummy_tree_0_1_2_3();

        assert_eq!(tree.get(&0).unwrap().value, 0);
        assert_eq!(tree.get(&1).unwrap().value, 1);
        assert_eq!(tree.get(&2).unwrap().value, 2);
        assert_eq!(tree.get(&3).unwrap().value, 3);
        assert_eq!(tree.get(&4), None);
    }

    #[test]
    fn test_get_mut() {
        let original = dummy_tree_0_1_2_3();
        let mut tree = original.clone();

        tree.get_mut(&2).unwrap().value = -2;
        tree.get_mut(&3).unwrap().value = -3;
        assert!(tree.get_mut(&4).is_none());

        assert_eq!(original.get(&0).unwrap().value, 0);
        assert_eq!(original.get(&1).unwrap().value, 1);
        assert_eq!(original.get(&2).unwrap().value, 2);
        assert_eq!(original.get(&3).unwrap().value, 3);
        assert_eq!(original.get(&4), None);

        assert_eq!(tree.get(&0).unwrap().value, 0);
        assert_eq!(tree.get(&1).unwrap().value, 1);
        assert_eq!(tree.get(&2).unwrap().value, -2);
        assert_eq!(tree.get(&3).unwrap().value, -3);
        assert_eq!(tree.get(&4), None);
    }

    #[test]
    fn test_first() {
        let tree = dummy_tree_0_1_2_3();

        assert_eq!(tree.first().key, 0);
    }

    #[test]
    fn test_last() {
        let tree = dummy_tree_0_1_2_3();

        assert_eq!(tree.last().key, 3);
    }

    #[allow(clippy::too_many_lines)]
    #[test]
    fn test_balance() {
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

        let entry_x = SharedPointer::new(Entry::new('x', ()));
        let entry_y = SharedPointer::new(Entry::new('y', ()));
        let entry_z = SharedPointer::new(Entry::new('z', ()));

        let tree_a = SharedPointer::new(Node::new_black(Entry::new('a', ())));
        let tree_b = SharedPointer::new(Node::new_black(Entry::new('b', ())));
        let tree_c = SharedPointer::new(Node::new_black(Entry::new('c', ())));
        let tree_d = SharedPointer::new(Node::new_black(Entry::new('d', ())));

        let mut tree_case_1: Node<_, _, RcK> = Node {
            entry: SharedPointer::clone(&entry_z),
            color: Color::Black,
            left: Some(SharedPointer::new(Node {
                entry: SharedPointer::clone(&entry_y),
                color: Color::Red,
                left: Some(SharedPointer::new(Node {
                    entry: SharedPointer::clone(&entry_x),
                    color: Color::Red,
                    left: Some(SharedPointer::clone(&tree_a)),
                    right: Some(SharedPointer::clone(&tree_b)),
                })),
                right: Some(SharedPointer::clone(&tree_c)),
            })),
            right: Some(SharedPointer::clone(&tree_d)),
        };

        let mut tree_case_2: Node<_, _, RcK> = Node {
            entry: SharedPointer::clone(&entry_z),
            color: Color::Black,
            left: Some(SharedPointer::new(Node {
                entry: SharedPointer::clone(&entry_x),
                color: Color::Red,
                left: Some(SharedPointer::clone(&tree_a)),
                right: Some(SharedPointer::new(Node {
                    entry: SharedPointer::clone(&entry_y),
                    color: Color::Red,
                    left: Some(SharedPointer::clone(&tree_b)),
                    right: Some(SharedPointer::clone(&tree_c)),
                })),
            })),
            right: Some(SharedPointer::clone(&tree_d)),
        };

        let mut tree_case_3: Node<_, _, RcK> = Node {
            entry: SharedPointer::clone(&entry_x),
            color: Color::Black,
            left: Some(SharedPointer::clone(&tree_a)),
            right: Some(SharedPointer::new(Node {
                entry: SharedPointer::clone(&entry_z),
                color: Color::Red,
                left: Some(SharedPointer::new(Node {
                    entry: SharedPointer::clone(&entry_y),
                    color: Color::Red,
                    left: Some(SharedPointer::clone(&tree_b)),
                    right: Some(SharedPointer::clone(&tree_c)),
                })),
                right: Some(SharedPointer::clone(&tree_d)),
            })),
        };

        let mut tree_case_4: Node<_, _, RcK> = Node {
            entry: SharedPointer::clone(&entry_x),
            color: Color::Black,
            left: Some(SharedPointer::clone(&tree_a)),
            right: Some(SharedPointer::new(Node {
                entry: SharedPointer::clone(&entry_y),
                color: Color::Red,
                left: Some(SharedPointer::clone(&tree_b)),
                right: Some(SharedPointer::new(Node {
                    entry: SharedPointer::clone(&entry_z),
                    color: Color::Red,
                    left: Some(SharedPointer::clone(&tree_c)),
                    right: Some(SharedPointer::clone(&tree_d)),
                })),
            })),
        };

        let mut tree_none_of_the_above: Node<_, _, RcK> = Node {
            entry: SharedPointer::clone(&entry_z),
            color: Color::Black,
            left: Some(SharedPointer::new(Node {
                entry: SharedPointer::clone(&entry_y),
                color: Color::Red,
                left: Some(SharedPointer::new(Node {
                    entry: SharedPointer::clone(&entry_x),
                    color: Color::Black,
                    left: Some(SharedPointer::clone(&tree_a)),
                    right: Some(SharedPointer::clone(&tree_b)),
                })),
                right: Some(SharedPointer::clone(&tree_c)),
            })),
            right: Some(SharedPointer::clone(&tree_d)),
        };

        let mut tree_balanced: Node<_, _, RcK> = Node {
            entry: SharedPointer::clone(&entry_y),
            color: Color::Red,
            left: Some(SharedPointer::new(Node {
                entry: SharedPointer::clone(&entry_x),
                color: Color::Black,
                left: Some(SharedPointer::clone(&tree_a)),
                right: Some(SharedPointer::clone(&tree_b)),
            })),
            right: Some(SharedPointer::new(Node {
                entry: SharedPointer::clone(&entry_z),
                color: Color::Black,
                left: Some(SharedPointer::clone(&tree_c)),
                right: Some(SharedPointer::clone(&tree_d)),
            })),
        };

        tree_case_1.balance();
        assert_eq!(tree_case_1, tree_balanced.clone());

        tree_case_2.balance();
        assert_eq!(tree_case_2, tree_balanced.clone());

        tree_case_3.balance();
        assert_eq!(tree_case_3, tree_balanced.clone());

        tree_case_4.balance();
        assert_eq!(tree_case_4, tree_balanced.clone());

        let tree_none_of_the_above_original = tree_none_of_the_above.clone();
        tree_none_of_the_above.balance();
        assert_eq!(tree_none_of_the_above, tree_none_of_the_above_original);

        let tree_balanced_original = tree_balanced.clone();
        tree_balanced.balance();
        assert_eq!(tree_balanced, tree_balanced_original);
    }

    #[test]
    fn test_insert() {
        let mut node = None;
        let is_new_key = Node::insert(&mut node, 0, 1);
        let expected_node: Node<_, _, RcK> = Node::new_black(Entry::new(0, 1));

        assert!(is_new_key);
        assert_eq!(node.as_ref().map(Borrow::borrow), Some(&expected_node));

        let is_new_key = Node::insert(&mut node, 0, 2);
        let expected_node: Node<_, _, RcK> = Node::new_black(Entry::new(0, 2));

        assert!(!is_new_key);
        assert_eq!(node.as_ref().map(Borrow::borrow), Some(&expected_node));

        let is_new_key = Node::insert(&mut node, 10, 3);
        let expected_node: Node<_, _, RcK> = Node {
            entry: SharedPointer::new(Entry::new(0, 2)),
            color: Color::Black,
            left: None,
            right: Some(SharedPointer::new(Node {
                entry: SharedPointer::new(Entry::new(10, 3)),
                color: Color::Red,
                left: None,
                right: None,
            })),
        };

        assert!(is_new_key);
        assert_eq!(node.as_ref().map(Borrow::borrow), Some(&expected_node));

        let is_new_key = Node::insert(&mut node, 10, 4);
        let expected_node: Node<_, _, RcK> = Node {
            entry: SharedPointer::new(Entry::new(0, 2)),
            color: Color::Black,
            left: None,
            right: Some(SharedPointer::new(Node {
                entry: SharedPointer::new(Entry::new(10, 4)),
                color: Color::Red,
                left: None,
                right: None,
            })),
        };

        assert!(!is_new_key);
        assert_eq!(node.as_ref().map(Borrow::borrow), Some(&expected_node));

        let is_new_key = Node::insert(&mut node, 5, 5);
        // It is going to get rebalanced (by case 3).
        let expected_node: Node<_, _, RcK> = Node {
            entry: SharedPointer::new(Entry::new(5, 5)),
            color: Color::Black,
            left: Some(SharedPointer::new(Node {
                entry: SharedPointer::new(Entry::new(0, 2)),
                color: Color::Black,
                left: None,
                right: None,
            })),
            right: Some(SharedPointer::new(Node {
                entry: SharedPointer::new(Entry::new(10, 4)),
                color: Color::Black,
                left: None,
                right: None,
            })),
        };

        assert!(is_new_key);
        assert_eq!(node.as_ref().map(Borrow::borrow), Some(&expected_node));

        let is_new_key = Node::insert(&mut node, 0, 1);
        // It is going to get rebalanced (by case 3).
        let expected_node: Node<_, _, RcK> = Node {
            entry: SharedPointer::new(Entry::new(5, 5)),
            color: Color::Black,
            left: Some(SharedPointer::new(Node {
                entry: SharedPointer::new(Entry::new(0, 1)),
                color: Color::Black,
                left: None,
                right: None,
            })),
            right: Some(SharedPointer::new(Node {
                entry: SharedPointer::new(Entry::new(10, 4)),
                color: Color::Black,
                left: None,
                right: None,
            })),
        };

        assert!(!is_new_key);
        assert_eq!(node.as_ref().map(Borrow::borrow), Some(&expected_node));
    }

    #[allow(clippy::too_many_lines)]
    #[test]
    fn test_remove_fuse() {
        let mut node = dummy_node("");

        assert!(!Node::remove_fuse(&mut node, None, None));

        let right = dummy_node("x");
        let expected_node = right.clone();

        assert!(Node::remove_fuse(&mut node, None, Some(SharedPointer::new(right))));
        assert_eq!(node, expected_node);

        let left = dummy_node("x");
        let expected_node = left.clone();

        assert!(Node::remove_fuse(&mut node, Some(SharedPointer::new(left)), None));
        assert_eq!(node, expected_node);

        let left = Node {
            entry: SharedPointer::new(dummy_entry("a")),
            color: Color::Black,
            left: None,
            right: None,
        };
        let right = Node {
            entry: SharedPointer::new(dummy_entry("x")),
            color: Color::Red,
            left: None,
            right: Some(SharedPointer::new(dummy_node("c"))),
        };
        let expected_node = Node {
            entry: SharedPointer::new(dummy_entry("x")),
            color: Color::Red,
            left: Some(SharedPointer::new(left.clone())),
            right: Some(SharedPointer::new(dummy_node("c"))),
        };

        assert!(Node::remove_fuse(
            &mut node,
            Some(SharedPointer::new(left)),
            Some(SharedPointer::new(right))
        ));
        assert_eq!(node, expected_node);

        let left = Node {
            entry: SharedPointer::new(dummy_entry("x")),
            color: Color::Red,
            left: Some(SharedPointer::new(dummy_node("a"))),
            right: None,
        };
        let right = Node {
            entry: SharedPointer::new(dummy_entry("c")),
            color: Color::Black,
            left: None,
            right: None,
        };
        let expected_node = Node {
            entry: SharedPointer::new(dummy_entry("x")),
            color: Color::Red,
            left: Some(SharedPointer::new(dummy_node("a"))),
            right: Some(SharedPointer::new(right.clone())),
        };

        assert!(Node::remove_fuse(
            &mut node,
            Some(SharedPointer::new(left)),
            Some(SharedPointer::new(right))
        ));
        assert_eq!(node, expected_node);

        let left = Node {
            entry: SharedPointer::new(dummy_entry("x")),
            color: Color::Red,
            left: Some(SharedPointer::new(dummy_node("a"))),
            right: None,
        };
        let right = Node {
            entry: SharedPointer::new(dummy_entry("y")),
            color: Color::Red,
            left: Some(SharedPointer::new(dummy_node("c").make_red())),
            right: Some(SharedPointer::new(dummy_node("d"))),
        };
        let expected_node = Node {
            entry: SharedPointer::new(dummy_entry("c")),
            color: Color::Red,
            left: Some(SharedPointer::new(Node {
                entry: SharedPointer::new(dummy_entry("x")),
                color: Color::Red,
                left: Some(SharedPointer::new(dummy_node("a"))),
                right: None,
            })),
            right: Some(SharedPointer::new(Node {
                entry: SharedPointer::new(dummy_entry("y")),
                color: Color::Red,
                left: None,
                right: Some(SharedPointer::new(dummy_node("d"))),
            })),
        };

        assert!(Node::remove_fuse(
            &mut node,
            Some(SharedPointer::new(left)),
            Some(SharedPointer::new(right))
        ));
        assert_eq!(node, expected_node);

        let left = Node {
            entry: SharedPointer::new(dummy_entry("x")),
            color: Color::Red,
            left: Some(SharedPointer::new(dummy_node("a"))),
            right: None,
        };
        let right = Node {
            entry: SharedPointer::new(dummy_entry("y")),
            color: Color::Red,
            left: Some(SharedPointer::new(dummy_node("c").make_black())),
            right: Some(SharedPointer::new(dummy_node("d"))),
        };
        let expected_node = Node {
            entry: SharedPointer::new(dummy_entry("x")),
            color: Color::Red,
            left: Some(SharedPointer::new(dummy_node("a"))),
            right: Some(SharedPointer::new(Node {
                entry: SharedPointer::new(dummy_entry("y")),
                color: Color::Red,
                left: Some(SharedPointer::new(dummy_node("c").make_black())),
                right: Some(SharedPointer::new(dummy_node("d"))),
            })),
        };

        assert!(Node::remove_fuse(
            &mut node,
            Some(SharedPointer::new(left)),
            Some(SharedPointer::new(right))
        ));
        assert_eq!(node, expected_node);

        let left = Node {
            entry: SharedPointer::new(dummy_entry("x")),
            color: Color::Black,
            left: Some(SharedPointer::new(dummy_node("a"))),
            right: None,
        };
        let right = Node {
            entry: SharedPointer::new(dummy_entry("y")),
            color: Color::Black,
            left: Some(SharedPointer::new(dummy_node("c").make_red())),
            right: Some(SharedPointer::new(dummy_node("d"))),
        };
        let expected_node = Node {
            entry: SharedPointer::new(dummy_entry("c")),
            color: Color::Red,
            left: Some(SharedPointer::new(Node {
                entry: SharedPointer::new(dummy_entry("x")),
                color: Color::Black,
                left: Some(SharedPointer::new(dummy_node("a"))),
                right: None,
            })),
            right: Some(SharedPointer::new(Node {
                entry: SharedPointer::new(dummy_entry("y")),
                color: Color::Black,
                left: None,
                right: Some(SharedPointer::new(dummy_node("d"))),
            })),
        };

        assert!(Node::remove_fuse(
            &mut node,
            Some(SharedPointer::new(left)),
            Some(SharedPointer::new(right))
        ));
        assert_eq!(node, expected_node);

        let left = Node {
            entry: SharedPointer::new(dummy_entry("x")),
            color: Color::Black,
            left: Some(SharedPointer::new(dummy_node("a"))),
            right: None,
        };
        let right = Node {
            entry: SharedPointer::new(dummy_entry("y")),
            color: Color::Black,
            left: Some(SharedPointer::new(dummy_node("c").make_black())),
            right: Some(SharedPointer::new(dummy_node("d"))),
        };
        let expected_node = {
            let mut n = Node {
                entry: SharedPointer::new(dummy_entry("x")),
                color: Color::Red,
                left: Some(SharedPointer::new(dummy_node("a"))),
                right: Some(SharedPointer::new(Node {
                    entry: SharedPointer::new(dummy_entry("y")),
                    color: Color::Black,
                    left: Some(SharedPointer::new(dummy_node("c").make_black())),
                    right: Some(SharedPointer::new(dummy_node("d"))),
                })),
            };
            n.remove_balance_left();
            n
        };

        assert!(Node::remove_fuse(
            &mut node,
            Some(SharedPointer::new(left)),
            Some(SharedPointer::new(right))
        ));
        assert_eq!(node, expected_node);
    }

    #[test]
    fn test_remove_balance() {
        let mut node = Node {
            entry: SharedPointer::new(dummy_entry("y")),
            color: Color::Black, // Irrelevant
            left: Some(SharedPointer::new(Node {
                entry: SharedPointer::new(dummy_entry("x")),
                color: Color::Red,
                left: Some(SharedPointer::new(dummy_node("a"))),
                right: Some(SharedPointer::new(dummy_node("b"))),
            })),
            right: Some(SharedPointer::new(Node {
                entry: SharedPointer::new(dummy_entry("z")),
                color: Color::Red,
                left: Some(SharedPointer::new(dummy_node("c"))),
                right: Some(SharedPointer::new(dummy_node("d"))),
            })),
        };
        let expected_node = Node {
            entry: SharedPointer::new(dummy_entry("y")),
            color: Color::Red,
            left: Some(SharedPointer::new(Node {
                entry: SharedPointer::new(dummy_entry("x")),
                color: Color::Black,
                left: Some(SharedPointer::new(dummy_node("a"))),
                right: Some(SharedPointer::new(dummy_node("b"))),
            })),
            right: Some(SharedPointer::new(Node {
                entry: SharedPointer::new(dummy_entry("z")),
                color: Color::Black,
                left: Some(SharedPointer::new(dummy_node("c"))),
                right: Some(SharedPointer::new(dummy_node("d"))),
            })),
        };

        node.remove_balance();
        assert_eq!(node, expected_node);
    }

    #[test]
    fn test_remove_balance_left() {
        let bl = Node {
            entry: SharedPointer::new(dummy_entry("bl")),
            color: Color::Black,
            left: None,
            right: None,
        };

        let mut node = Node {
            entry: SharedPointer::new(dummy_entry("y")),
            color: Color::Black, // Irrelevant
            left: Some(SharedPointer::new(Node {
                entry: SharedPointer::new(dummy_entry("x")),
                color: Color::Red,
                left: Some(SharedPointer::new(dummy_node("a"))),
                right: Some(SharedPointer::new(dummy_node("b"))),
            })),
            right: Some(SharedPointer::new(dummy_node("c"))),
        };
        let expected_node = Node {
            entry: SharedPointer::new(dummy_entry("y")),
            color: Color::Red,
            left: Some(SharedPointer::new(Node {
                entry: SharedPointer::new(dummy_entry("x")),
                color: Color::Black,
                left: Some(SharedPointer::new(dummy_node("a"))),
                right: Some(SharedPointer::new(dummy_node("b"))),
            })),
            right: Some(SharedPointer::new(dummy_node("c"))),
        };

        node.remove_balance_left();
        assert_eq!(node, expected_node);

        let mut node = Node {
            entry: SharedPointer::new(dummy_entry("x")),
            color: Color::Black, // Irrelevant
            left: Some(SharedPointer::new(bl.clone())),
            right: Some(SharedPointer::new(Node {
                entry: SharedPointer::new(dummy_entry("y")),
                color: Color::Black,
                left: Some(SharedPointer::new(dummy_node("a"))),
                right: Some(SharedPointer::new(dummy_node("b"))),
            })),
        };
        let expected_node = {
            let mut n = Node {
                entry: SharedPointer::new(dummy_entry("x")),
                color: Color::Black,
                left: Some(SharedPointer::new(bl.clone())),
                right: Some(SharedPointer::new(Node {
                    entry: SharedPointer::new(dummy_entry("y")),
                    color: Color::Red,
                    left: Some(SharedPointer::new(dummy_node("a"))),
                    right: Some(SharedPointer::new(dummy_node("b"))),
                })),
            };
            n.remove_balance();
            n
        };

        node.remove_balance_left();
        assert_eq!(node, expected_node);

        let mut node = Node {
            entry: SharedPointer::new(dummy_entry("x")),
            color: Color::Black, // Irrelevant
            left: Some(SharedPointer::new(bl.clone())),
            right: Some(SharedPointer::new(Node {
                entry: SharedPointer::new(dummy_entry("z")),
                color: Color::Red,
                left: Some(SharedPointer::new(Node {
                    entry: SharedPointer::new(dummy_entry("y")),
                    color: Color::Black,
                    left: Some(SharedPointer::new(dummy_node("a"))),
                    right: Some(SharedPointer::new(dummy_node("b"))),
                })),
                right: Some(SharedPointer::new(dummy_node("c").make_black())),
            })),
        };
        let expected_node = Node {
            entry: SharedPointer::new(dummy_entry("y")),
            color: Color::Red,
            left: Some(SharedPointer::new(Node {
                entry: SharedPointer::new(dummy_entry("x")),
                color: Color::Black,
                left: Some(SharedPointer::new(bl.clone())),
                right: Some(SharedPointer::new(dummy_node("a"))),
            })),
            right: Some(SharedPointer::new({
                let mut n = Node {
                    entry: SharedPointer::new(dummy_entry("z")),
                    color: Color::Black,
                    left: Some(SharedPointer::new(dummy_node("b"))),
                    right: Some(SharedPointer::new(dummy_node("c").make_red())),
                };
                n.remove_balance();
                n
            })),
        };

        node.remove_balance_left();
        assert_eq!(node, expected_node);
    }

    #[test]
    fn test_remove_balance_right() {
        let bl = Node {
            entry: SharedPointer::new(dummy_entry("bl")),
            color: Color::Black,
            left: None,
            right: None,
        };

        let mut node = Node {
            entry: SharedPointer::new(dummy_entry("x")),
            color: Color::Black, // Irrelevant
            left: Some(SharedPointer::new(dummy_node("a"))),
            right: Some(SharedPointer::new(Node {
                entry: SharedPointer::new(dummy_entry("y")),
                color: Color::Red,
                left: Some(SharedPointer::new(dummy_node("b"))),
                right: Some(SharedPointer::new(dummy_node("c"))),
            })),
        };
        let expected_node = Node {
            entry: SharedPointer::new(dummy_entry("x")),
            color: Color::Red,
            left: Some(SharedPointer::new(dummy_node("a"))),
            right: Some(SharedPointer::new(Node {
                entry: SharedPointer::new(dummy_entry("y")),
                color: Color::Black,
                left: Some(SharedPointer::new(dummy_node("b"))),
                right: Some(SharedPointer::new(dummy_node("c"))),
            })),
        };

        node.remove_balance_right();
        assert_eq!(node, expected_node);

        let mut node = Node {
            entry: SharedPointer::new(dummy_entry("y")),
            color: Color::Black, // Irrelevant
            left: Some(SharedPointer::new(Node {
                entry: SharedPointer::new(dummy_entry("x")),
                color: Color::Black,
                left: Some(SharedPointer::new(dummy_node("a"))),
                right: Some(SharedPointer::new(dummy_node("b"))),
            })),
            right: Some(SharedPointer::new(bl.clone())),
        };
        let expected_node = {
            let mut n = Node {
                entry: SharedPointer::new(dummy_entry("y")),
                color: Color::Black,
                left: Some(SharedPointer::new(Node {
                    entry: SharedPointer::new(dummy_entry("x")),
                    color: Color::Red,
                    left: Some(SharedPointer::new(dummy_node("a"))),
                    right: Some(SharedPointer::new(dummy_node("b"))),
                })),
                right: Some(SharedPointer::new(bl.clone())),
            };
            n.remove_balance();
            n
        };

        node.remove_balance_right();
        assert_eq!(node, expected_node);

        let mut node = Node {
            entry: SharedPointer::new(dummy_entry("z")),
            color: Color::Black, // Irrelevant
            left: Some(SharedPointer::new(Node {
                entry: SharedPointer::new(dummy_entry("x")),
                color: Color::Red,
                left: Some(SharedPointer::new(dummy_node("a").make_black())),
                right: Some(SharedPointer::new(Node {
                    entry: SharedPointer::new(dummy_entry("y")),
                    color: Color::Black,
                    left: Some(SharedPointer::new(dummy_node("b"))),
                    right: Some(SharedPointer::new(dummy_node("c"))),
                })),
            })),
            right: Some(SharedPointer::new(bl.clone())),
        };
        let expected_node = Node {
            entry: SharedPointer::new(dummy_entry("y")),
            color: Color::Red,
            left: Some(SharedPointer::new({
                let mut n = Node {
                    entry: SharedPointer::new(dummy_entry("x")),
                    color: Color::Black,
                    left: Some(SharedPointer::new(dummy_node("a").make_red())),
                    right: Some(SharedPointer::new(dummy_node("b"))),
                };
                n.remove_balance();
                n
            })),
            right: Some(SharedPointer::new(Node {
                entry: SharedPointer::new(dummy_entry("z")),
                color: Color::Black,
                left: Some(SharedPointer::new(dummy_node("c"))),
                right: Some(SharedPointer::new(bl.clone())),
            })),
        };

        node.remove_balance_right();
        assert_eq!(node, expected_node);
    }
}

mod internal {
    use super::*;
    use alloc::vec::Vec;
    use pretty_assertions::assert_eq;

    fn insert_test(values: &[u32]) {
        let mut map = RedBlackTreeMap::new();

        for (i, &v) in values.iter().enumerate() {
            map.insert_mut(v, 2 * v);

            let other_v = values[i / 2];

            assert_eq!(map.get(&v), Some(&(2 * v)));
            assert_eq!(map.get(&other_v), Some(&(2 * other_v)));

            if let Err(error) = map.check_consistent() {
                panic!(
                    "Consistency error in red-black tree ({:?}).  Insertions: {:?}",
                    error,
                    &values[0..=i]
                );
            }
        }
    }

    #[test]
    fn test_insert_sorted() {
        let vec: Vec<u32> = (0..4092).collect();
        insert_test(&vec);
    }

    #[test]
    fn test_insert() {
        use rand::SeedableRng;
        use rand::rngs::StdRng;
        use rand::seq::SliceRandom;

        let limit = 25_000;
        let seed: [u8; 32] = [
            24, 73, 23, 5, 34, 57, 253, 46, 245, 73, 23, 155, 137, 250, 46, 46, 217, 3, 55, 157,
            137, 250, 46, 46, 217, 3, 55, 157, 34, 135, 34, 123,
        ];
        let mut rng: StdRng = SeedableRng::from_seed(seed);
        let mut permutation: [u32; 64] = {
            let mut p: [u32; 64] = [0; 64];

            for i in 0..64 {
                p[i as usize] = i;
            }

            p
        };

        for _ in 0..limit {
            permutation.shuffle(&mut rng);

            insert_test(&permutation);
        }
    }

    fn remove_test(values_insert: &[u32], values_remove: &[u32]) {
        let mut map = RedBlackTreeMap::new();

        for &v in values_insert {
            map.insert_mut(v, 2 * v);
        }

        for (i, v) in values_remove.iter().enumerate() {
            map.remove_mut(v);

            assert!(!map.contains_key(v));

            if let Err(error) = map.check_consistent() {
                panic!(
                    "Consistency error in red-black tree ({:?}).  Insertions: {:?}.  Removals: {:?}",
                    error,
                    &values_insert,
                    &values_remove[0..=i]
                );
            }
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
        use rand::SeedableRng;
        use rand::rngs::StdRng;
        use rand::seq::SliceRandom;

        let limit = 25_000;
        let seed: [u8; 32] = [
            24, 73, 23, 5, 34, 57, 253, 46, 245, 73, 23, 155, 137, 250, 46, 46, 217, 3, 55, 157,
            137, 250, 46, 46, 217, 3, 55, 157, 34, 135, 34, 123,
        ];
        let mut rng: StdRng = SeedableRng::from_seed(seed);
        let mut permutation_insert: [u32; 64] = {
            let mut p: [u32; 64] = [0; 64];

            for i in 0..64 {
                p[i as usize] = i;
            }

            p
        };
        let mut permutation_remove: [u32; 64] = permutation_insert;

        for _ in 0..limit {
            permutation_insert.shuffle(&mut rng);
            permutation_remove.shuffle(&mut rng);

            remove_test(&permutation_insert, &permutation_remove);
        }
    }
}

mod iter {
    use super::*;
    use alloc::vec::Vec;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_lg_floor() {
        assert_eq!(iter_utils::lg_floor(1), 0);
        assert_eq!(iter_utils::lg_floor(2), 1);
        assert_eq!(iter_utils::lg_floor(3), 1);
        assert_eq!(iter_utils::lg_floor(4), 2);
        assert_eq!(iter_utils::lg_floor(5), 2);
        assert_eq!(iter_utils::lg_floor(7), 2);
        assert_eq!(iter_utils::lg_floor(8), 3);
        assert_eq!(iter_utils::lg_floor(9), 3);
        assert_eq!(iter_utils::lg_floor(15), 3);
        assert_eq!(iter_utils::lg_floor(16), 4);
        assert_eq!(iter_utils::lg_floor(17), 4);
    }

    #[allow(clippy::explicit_iter_loop)]
    #[allow(clippy::never_loop)]
    #[test]
    fn test_iter_empty() {
        let map: RedBlackTreeMap<i32, i32> = RedBlackTreeMap::new();

        for _ in map.iter() {
            panic!("iterator should be empty");
        }
    }

    #[allow(clippy::never_loop)]
    #[test]
    fn test_iter_empty_backwards() {
        let map: RedBlackTreeMap<i32, i32> = RedBlackTreeMap::new();

        for _ in map.iter().rev() {
            panic!("iterator should be empty");
        }
    }

    #[allow(clippy::explicit_iter_loop)]
    #[test]
    fn test_iter_big_map() {
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
    fn test_iter_big_map_backwards() {
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
    fn test_iter_both_directions() {
        let map = rbt_map![
            0 => 10,
            1 => 11,
            2 => 12,
            3 => 13,
            4 => 14,
            5 => 15
        ];
        let mut iterator = map.iter();

        assert_eq!(iterator.next(), Some((&0, &10)));
        assert_eq!(iterator.next_back(), Some((&5, &15)));
        assert_eq!(iterator.next_back(), Some((&4, &14)));
        assert_eq!(iterator.next(), Some((&1, &11)));
        assert_eq!(iterator.next(), Some((&2, &12)));
        assert_eq!(iterator.next_back(), Some((&3, &13)));
        assert_eq!(iterator.next_back(), None);
        assert_eq!(iterator.next(), None);
    }

    #[test]
    fn test_iter_size_hint() {
        let map = rbt_map![
            0 => 10,
            1 => 11,
            2 => 12
        ];
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
    fn test_iter_sorted() {
        let map = rbt_map![
            5 => (),
            6 => (),
            2 => (),
            1 => ()
        ];
        let mut iterator = map.iter();

        assert_eq!(iterator.next(), Some((&1, &())));
        assert_eq!(iterator.next(), Some((&2, &())));
        assert_eq!(iterator.next(), Some((&5, &())));
        assert_eq!(iterator.next(), Some((&6, &())));
        assert_eq!(iterator.next(), None);
    }

    #[test]
    fn test_iter_keys() {
        let map = rbt_map![
            0 => 10,
            1 => 11,
            2 => 12
        ];
        let mut iter = map.keys();

        assert_eq!(iter.next(), Some(&0));
        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.next(), Some(&2));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_iter_values() {
        let map = rbt_map![
            10 => 0,
            11 => 1,
            12 => 2
        ];
        let mut iter = map.values();

        assert_eq!(iter.next(), Some(&0));
        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.next(), Some(&2));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_into_iterator() {
        let map = rbt_map![
            0 => 0,
            1 => 2,
            2 => 4,
            3 => 6
        ];
        let mut left = 4;

        for (expected, (k, v)) in map.into_iter().enumerate() {
            left -= 1;

            assert!(left >= 0);
            assert_eq!(*k, expected);
            assert_eq!(*v, 2 * expected);
        }

        assert_eq!(left, 0);
    }

    #[test]
    fn test_range() {
        use core::ops::Bound::*;

        fn cmp<RB: RangeBounds<i32> + Clone>(
            map: &RedBlackTreeMap<i32, i32>,
            range: RB,
            expected: &[(i32, i32)],
        ) {
            assert_eq!(
                map.range(range.clone()).map(|(k, v)| (*k, *v)).collect::<Vec<_>>(),
                expected
            );
            assert_eq!(
                map.range(range).rev().map(|(k, v)| (*k, *v)).collect::<Vec<_>>(),
                expected.iter().copied().rev().collect::<Vec<_>>()
            );
        }

        let map = rbt_map![
            0 => 0,
            1 => 2,
            2 => 4,
            3 => 6
        ];

        cmp(&map, .., &[(0, 0), (1, 2), (2, 4), (3, 6)]);
        cmp(&map, 1.., &[(1, 2), (2, 4), (3, 6)]);
        cmp(&map, 1..3, &[(1, 2), (2, 4)]);
        cmp(&map, 1..=3, &[(1, 2), (2, 4), (3, 6)]);
        cmp(&map, ..3, &[(0, 0), (1, 2), (2, 4)]);

        cmp(&map, (Excluded(1), Included(3)), &[(2, 4), (3, 6)]);
    }

    #[test]
    fn test_range_empty() {
        let map = rbt_map![
            0 => 0,
            1 => 2,
            10 => 20,
            11 => 22
        ];

        assert_eq!(map.range(1..1).next(), None);
        assert_eq!(map.range(3..10).next(), None);
        assert_eq!(map.range(..0).next(), None);
        assert_eq!(map.range(3..=9).next(), None);
        assert_eq!(map.range(13..).next(), None);
    }
}

#[test]
fn test_macro_rbt_map() {
    let set_1 = RedBlackTreeMap::new().insert(1, 2);
    let set_1_2_3 = RedBlackTreeMap::new().insert(1, 2).insert(2, 3).insert(3, 4);

    assert_eq!(RedBlackTreeMap::<u32, u32>::new(), rbt_map![]);
    assert_eq!(set_1, rbt_map![1 => 2]);
    assert_eq!(set_1_2_3, rbt_map![1 => 2, 2 => 3, 3 => 4]);
}

#[test]
fn test_get_key_value() {
    let mut map = RedBlackTreeMap::new();

    map = map.insert("foo", 4);
    assert_eq!(map.get_key_value("foo"), Some((&"foo", &4)));

    map = map.insert("bar", 2);
    assert_eq!(map.get_key_value("foo"), Some((&"foo", &4)));
    assert_eq!(map.get_key_value("bar"), Some((&"bar", &2)));
}

#[test]
fn test_insert_simple() {
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
fn test_insert() {
    let mut map = RedBlackTreeMap::new();

    // These are relatively small limits.  We prefer to do a more hardcore test in the mutable
    // version.
    let limit = 5_000;
    let overwrite_limit = 1_000;

    for i in 0..limit {
        map = map.insert(i, -i);

        assert_eq!(map.size(), (i as usize) + 1);
        assert_eq!(map.get(&i), Some(&-i));

        // Lets also check a previous value.
        let prev_key = i / 2;
        assert_eq!(map.get(&prev_key), Some(&-prev_key));
    }

    // Now we test some overwrites.

    for i in 0..overwrite_limit {
        assert_eq!(map.get(&i), Some(&-i));

        map = map.insert(i, 2 * i);

        assert_eq!(map.size(), limit as usize);
        assert_eq!(map.get(&i), Some(&(2 * i)));
    }
}

#[test]
fn test_insert_mut_simple() {
    let mut map = RedBlackTreeMap::new();
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

    assert!(map.contains_key("baz"));
}

#[test]
fn test_insert_mut() {
    let mut map = RedBlackTreeMap::new();
    let limit = 25_000;
    let overwrite_limit = 5_000;

    for i in 0..limit {
        map.insert_mut(i, -i);

        assert_eq!(map.size(), (i as usize) + 1);
        assert_eq!(map.get(&i), Some(&-i));

        // Lets also check a previous value.
        let prev_key = i / 2;
        assert_eq!(map.get(&prev_key), Some(&-prev_key));
    }

    // Now we test some overwrites.

    for i in 0..overwrite_limit {
        assert_eq!(map.get(&i), Some(&-i));

        map.insert_mut(i, 2 * i);

        assert_eq!(map.size(), limit as usize);
        assert_eq!(map.get(&i), Some(&(2 * i)));
    }
}

#[test]
fn test_contains_key() {
    let map = rbt_map!["foo" => 7];

    assert!(map.contains_key("foo"));
    assert!(!map.contains_key("baz"));
}

#[test]
fn test_remove_simple() {
    let mut map = rbt_map![
        "foo" => 4,
        "bar" => 12,
        "mumble" => 13,
        "baz" => 42
    ];
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
fn test_remove() {
    let mut map = RedBlackTreeMap::new();

    // These are relatively small limits.  We prefer to do a more hardcore test in the mutable
    // version.
    let limit = 5_000;

    for i in 0..limit {
        map = map.insert(i, -i);
    }

    // Now lets remove half of it.

    for i in (0..limit / 2).map(|i| 2 * i) {
        assert_eq!(map.get(&i), Some(&-i));

        map = map.remove(&i);

        assert!(!map.contains_key(&i));
        assert_eq!(map.size(), (limit - i / 2 - 1) as usize);

        // Also check than the previous one is ok.
        if i > 0 {
            assert_eq!(map.get(&(i - 1)), Some(&-(i - 1)));
        }
    }
}

#[test]
fn test_remove_mut_simple() {
    let mut map = rbt_map![
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

#[test]
fn test_remove_mut() {
    let mut map = RedBlackTreeMap::new();
    let limit = 25_000;

    for i in 0..limit {
        map.insert_mut(i, -i);
    }

    // Now lets remove half of it.

    for i in (0..limit / 2).map(|i| 2 * i) {
        assert_eq!(map.get(&i), Some(&-i));

        map.remove_mut(&i);

        assert!(!map.contains_key(&i));
        assert_eq!(map.size(), (limit - i / 2 - 1) as usize);

        // Also check than the previous one is ok.
        if i > 0 {
            assert_eq!(map.get(&(i - 1)), Some(&-(i - 1)));
        }
    }
}

#[test]
fn test_first() {
    let map = rbt_map![5 => "hello", 12 => "there"];

    assert_eq!(map.first(), Some((&5, &"hello")));
}

#[test]
fn test_last() {
    let map = rbt_map![5 => "hello", 12 => "there"];

    assert_eq!(map.last(), Some((&12, &"there")));
}

#[test]
fn test_index() {
    let map = rbt_map![5 => "hello", 12 => "there"];

    assert_eq!(map[&5], "hello");
    assert_eq!(map[&12], "there");
}

#[test]
fn test_from_iterator() {
    let vec: Vec<(i32, &str)> = vec![(2, "two"), (5, "five")];
    let map: RedBlackTreeMap<i32, &str> = vec.iter().copied().collect();
    let expected_map = rbt_map![2 => "two", 5 => "five"];

    assert_eq!(map, expected_map);
}

#[test]
fn test_default() {
    let map: RedBlackTreeMap<u32, char> = RedBlackTreeMap::default();

    assert_eq!(map.size(), 0);
    assert!(map.is_empty());
}

#[test]
fn test_display() {
    let empty_map: RedBlackTreeMap<i32, i32> = RedBlackTreeMap::new();
    let singleton_map = rbt_map!["hi" => "hello"];
    let map = rbt_map![5 => "hello", 12 => "there"];

    assert_eq!(format!("{}", empty_map), "{}");
    assert_eq!(format!("{}", singleton_map), "{hi: hello}");
    assert_eq!(format!("{}", map), "{5: hello, 12: there}");
}

#[test]
fn test_eq() {
    let map_1 = rbt_map!["a" => 0xa, "b" => 0xb];
    let map_1_prime = rbt_map!["a" => 0xa, "b" => 0xb];
    let map_1_prime_2 = rbt_map!["a" => 0xa, "b" => 0xb, "b" => 0xb];
    let map_2 = rbt_map!["a" => 0xa, "b" => 0xb + 1];
    let map_3 = rbt_map!["a" => 0xa, "b" => 0xb + 1, "c" => 0xc];

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
    let map_a = rbt_map!["a" => 0];
    let map_a_sync = rbt_map_sync!["a" => 0];
    let map_b = rbt_map!["b" => 1];
    let map_b_sync = rbt_map_sync!["b" => 1];

    assert!(map_a == map_a_sync);
    assert!(map_a != map_b_sync);
    assert!(map_b == map_b_sync);
}

#[test]
fn test_partial_ord() {
    let map_1 = rbt_map!["a" => 0xa];
    let map_1_prime = rbt_map!["a" => 0xa];
    let map_2 = rbt_map!["b" => 0xb];
    let map_3 = rbt_map![0 => 0.0];
    let map_4 = rbt_map![0 => f32::NAN];

    assert_eq!(map_1.partial_cmp(&map_1_prime), Some(Ordering::Equal));
    assert_eq!(map_1.partial_cmp(&map_2), Some(Ordering::Less));
    assert_eq!(map_2.partial_cmp(&map_1), Some(Ordering::Greater));
    assert_eq!(map_3.partial_cmp(&map_4), None);
}

#[test]
fn test_ord() {
    let map_1 = rbt_map!["a" => 0xa];
    let map_1_prime = rbt_map!["a" => 0xa];
    let map_2 = rbt_map!["b" => 0xb];

    assert_eq!(map_1.cmp(&map_1_prime), Ordering::Equal);
    assert_eq!(map_1.cmp(&map_2), Ordering::Less);
    assert_eq!(map_2.cmp(&map_1), Ordering::Greater);
}

#[test]
fn test_ord_pointer_kind_consistent() {
    let map_a = rbt_map!["a" => 0];
    let map_a_sync = rbt_map_sync!["a" => 0];
    let map_b = rbt_map!["b" => 1];
    let map_b_sync = rbt_map_sync!["b" => 1];

    assert!(map_a <= map_a_sync);
    assert!(map_a < map_b_sync);
    assert!(map_b >= map_b_sync);

    assert!(map_a_sync >= map_a);
    assert!(map_b_sync > map_a);
    assert!(map_b_sync <= map_b);
}

fn hash<K: Ord + Hash, V: Hash, P>(map: &RedBlackTreeMap<K, V, P>) -> u64
where
    P: SharedPointerKind,
{
    #[allow(deprecated)]
    let mut hasher = core::hash::SipHasher::new();

    map.hash(&mut hasher);

    hasher.finish()
}

#[test]
fn test_hash() {
    let map_1 = rbt_map!["a" => 0xa];
    let map_1_prime = rbt_map!["a" => 0xa];
    let map_2 = rbt_map!["b" => 0xb, "a" => 0xa];

    assert_eq!(hash(&map_1), hash(&map_1));
    assert_eq!(hash(&map_1), hash(&map_1_prime));
    assert_ne!(hash(&map_1), hash(&map_2));
}

#[test]
fn test_hash_pointer_kind_consistent() {
    let map = rbt_map!["a" => 0];
    let map_sync = rbt_map_sync!["a" => 0];

    assert_eq!(hash(&map), hash(&map_sync));
}

#[test]
fn test_clone() {
    let map = rbt_map!["hello" => 4, "there" => 5];
    let clone = map.clone();

    assert_eq!(clone.size(), map.size());
    assert_eq!(clone.get("hello"), Some(&4));
    assert_eq!(clone.get("there"), Some(&5));
}

#[cfg(feature = "serde")]
#[test]
fn test_serde() {
    let map: RedBlackTreeMap<i32, i32> = rbt_map![5 => 6, 7 => 8, 9 => 10, 11 => 12];
    let encoded = serde_json::to_string(&map).unwrap();
    let decoded: RedBlackTreeMap<i32, i32> = serde_json::from_str(&encoded).unwrap();

    assert_eq!(map, decoded);
}
