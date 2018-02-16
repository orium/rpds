/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use std::sync::Arc;
use std::cmp::Ordering;
use std::borrow::Borrow;
use std::iter::FromIterator;
use std::ops::Index;
use std::fmt::Display;
use std::hash::{Hasher, Hash};
use super::entry::Entry;

// TODO Use impl trait instead of this when available.
pub type IterKeys<'a, K, V>   = ::std::iter::Map<Iter<'a, K, V>, fn((&'a K, &V)) -> &'a K>;
pub type IterValues<'a, K, V> = ::std::iter::Map<Iter<'a, K, V>, fn((&K, &'a V)) -> &'a V>;

/// Creates a [`RedBlackTreeMap`](map/red_black_tree_map/struct.RedBlackTreeMap.html) containing the
/// given arguments:
///
/// ```
/// # use rpds::*;
/// #
/// let m = RedBlackTreeMap::new()
///     .insert(1, "one")
///     .insert(2, "two")
///     .insert(3, "three");
///
/// assert_eq!(rbt_map![1 => "one", 2 => "two", 3 => "three"], m);
/// ```
#[macro_export]
macro_rules! rbt_map {
    ($($k:expr => $v:expr),*) => {
        {
            #[allow(unused_mut)]
            let mut m = $crate::RedBlackTreeMap::new();
            $(
                m = m.insert($k, $v);
            )*
            m
        }
    };
}

/// A persistent map with structural sharing.  This implementation uses a
/// [red-black tree](https://en.wikipedia.org/wiki/Red-Black_tree)
/// and supports fast `insert()`, `remove()`, and `get()`.
///
/// # Complexity
///
/// Let *n* be the number of elements in the map.
///
/// ## Temporal complexity
///
/// | Operation                  | Best case | Average   | Worst case  |
/// |:-------------------------- | ---------:| ---------:| -----------:|
/// | `new()`                    |      Θ(1) |      Θ(1) |        Θ(1) |
/// | `insert()`                 |      Θ(1) | Θ(log(n)) |   Θ(log(n)) |
/// | `remove()`                 |      Θ(1) | Θ(log(n)) |   Θ(log(n)) |
/// | `get()`                    |      Θ(1) | Θ(log(n)) |   Θ(log(n)) |
/// | `contains_key()`           |      Θ(1) | Θ(log(n)) |   Θ(log(n)) |
/// | `size()`                   |      Θ(1) |      Θ(1) |        Θ(1) |
/// | `clone()`                  |      Θ(1) |      Θ(1) |        Θ(1) |
/// | iterator creation          |      Θ(1) |      Θ(1) |        Θ(1) |
/// | iterator step              |      Θ(1) |      Θ(1) |   Θ(log(n)) |
/// | iterator full              |      Θ(n) |      Θ(n) |        Θ(n) |
///
/// # Implementation details
///
/// This implementation uses a [red-black tree](https://en.wikipedia.org/wiki/Red-Black_tree) as
/// described in "Purely Functional Data Structures" by Chris Okasaki, page 27.  Deletion is
/// implemented according to the paper "Red-Black Trees with Types" by Stefan Kahrs
/// ([reference implementation](https://www.cs.kent.ac.uk/people/staff/smk/redblack/Untyped.hs))
#[derive(Debug)]
pub struct RedBlackTreeMap<K, V> {
    root: Option<Arc<Node<K, V>>>,
    size: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Color {
    Red,
    Black,
}

#[derive(Debug, PartialEq, Eq)]
struct Node<K, V> {
    entry: Arc<Entry<K, V>>,
    color: Color,
    left:  Option<Arc<Node<K, V>>>,
    right: Option<Arc<Node<K, V>>>,
}

impl<K, V> Clone for Node<K, V> {
    fn clone(&self) -> Node<K, V> {
        Node {
            entry: Arc::clone(&self.entry),
            color: self.color,
            left:  self.left.clone(),
            right: self.right.clone(),
        }
    }
}

impl<K, V> Node<K, V>
    where K: Ord {
    fn new_red(entry: Entry<K, V>) -> Node<K, V> {
        Node {
            entry: Arc::new(entry),
            color: Color::Red,
            left:  None,
            right: None,
        }
    }

    fn borrow(node: &Option<Arc<Node<K, V>>>) -> Option<&Node<K, V>> {
        node.as_ref().map(|n| n.borrow())
    }

    fn left_color(&self) -> Option<Color> {
        self.left.as_ref().map(|l| l.color)
    }

    fn right_color(&self) -> Option<Color> {
        self.right.as_ref().map(|r| r.color)
    }

    fn with_entry(&self, entry: Entry<K, V>) -> Node<K, V> {
        Node {
            entry: Arc::new(entry),
            color: self.color,
            left:  self.left.clone(),
            right: self.right.clone(),
        }
    }

    fn with_left(&self, left: Node<K, V>) -> Node<K, V> {
        Node {
            entry: Arc::clone(&self.entry),
            color: self.color,
            left:  Some(Arc::new(left)),
            right: self.right.clone(),
        }
    }

    fn with_right(&self, right: Node<K, V>) -> Node<K, V> {
        Node {
            entry: Arc::clone(&self.entry),
            color: self.color,
            left:  self.left.clone(),
            right: Some(Arc::new(right)),
        }
    }

    fn make_black(self) -> Node<K, V> {
        let mut node = self;
        node.color = Color::Black;
        node
    }

    fn make_red(self) -> Node<K, V> {
        let mut node = self;
        node.color = Color::Red;
        node
    }

    fn get<Q: ?Sized>(&self, key: &Q) -> Option<&Entry<K, V>>
        where K: Borrow<Q>,
              Q: Ord {
        match key.cmp(self.entry.key.borrow()) {
            Ordering::Less    => self.left.as_ref().and_then(|l| l.get(key)),
            Ordering::Equal   => Some(&self.entry),
            Ordering::Greater => self.right.as_ref().and_then(|r| r.get(key)),
        }
    }

    fn first(&self) -> &Entry<K, V> {
        match self.left {
            Some(ref l) => l.first(),
            None => &self.entry,
        }
    }

    fn last(&self) -> &Entry<K, V> {
        match self.right {
            Some(ref r) => r.last(),
            None => &self.entry,
        }
    }

    /// Balances an unbalanced node.  This is a function is described in "Purely Functional
    /// Data Structures" by Chris Okasaki, page 27.
    ///
    /// The transformation is done as the figure below shows.
    ///
    /// ```text
    ///                                                                    ╭────────────────────╮
    ///                                                                    │  ┌───┐             │
    ///                                                                    │  │   │ Red node    │
    ///                                                                    │  └───┘             │
    ///            ┏━━━┓                                                   │                    │
    ///            ┃ z ┃                                                   │  ┏━━━┓             │
    ///            ┗━━━┛                                                   │  ┃   ┃ Black node  │
    ///             ╱ ╲                                                    │  ┗━━━┛             │
    ///        ┌───┐   d                                                   ╰────────────────────╯
    ///        │ y │                      Case 1
    ///        └───┘           ╭──────────────────────────────────────────────────╮
    ///         ╱ ╲            ╰────────────────────────────────────────────────╮ │
    ///     ┌───┐  c                                                            │ │
    ///     │ x │                                                               │ │
    ///     └───┘                                                               │ │
    ///      ╱ ╲                                                                │ │
    ///     a   b                                                               │ │
    ///                                                                         │ │
    ///                                                                         │ │
    ///                                                                         │ │
    ///            ┏━━━┓                                                        │ │
    ///            ┃ z ┃                                                        │ │
    ///            ┗━━━┛                                                        │ │
    ///             ╱ ╲                                                         │ │
    ///        ┌───┐   d                  Case 2                                │ │
    ///        │ x │           ╭─────────────────────────────╲                  │ │
    ///        └───┘           ╰────────────────────────────╲ ╲                 ╲ ╱
    ///         ╱ ╲                                          ╲ ╲
    ///        a  ┌───┐                                       ╲ ╲
    ///           │ y │                                        ╲ ╲             ┌───┐
    ///           └───┘                                         ╲ ╲            │ y │
    ///            ╱ ╲                                           ╲  ┃          └───┘
    ///           b   c                                          ───┘           ╱ ╲
    ///                                                                        ╱   ╲
    ///                                                                   ┏━━━┓     ┏━━━┓
    ///                                                                   ┃ x ┃     ┃ z ┃
    ///            ┏━━━┓                                                  ┗━━━┛     ┗━━━┛
    ///            ┃ x ┃                                         ───┐      ╱ ╲       ╱ ╲
    ///            ┗━━━┛                                         ╱  ┃     ╱   ╲     ╱   ╲
    ///             ╱ ╲                                         ╱ ╱      a     b   c     d
    ///            a  ┌───┐                                    ╱ ╱
    ///               │ z │                                   ╱ ╱
    ///               └───┘               Case 3             ╱ ╱                ╱ ╲
    ///                ╱ ╲     ╭────────────────────────────╱ ╱                 │ │
    ///            ┌───┐  d    ╰─────────────────────────────╱                  │ │
    ///            │ y │                                                        │ │
    ///            └───┘                                                        │ │
    ///             ╱ ╲                                                         │ │
    ///            b   c                                                        │ │
    ///                                                                         │ │
    ///                                                                         │ │
    ///                                                                         │ │
    ///            ┏━━━┓                                                        │ │
    ///            ┃ x ┃                                                        │ │
    ///            ┗━━━┛                                                        │ │
    ///             ╱ ╲                                                         │ │
    ///            a  ┌───┐               Case 4                                │ │
    ///               │ y │    ╭────────────────────────────────────────────────┘ │
    ///               └───┘    ╰──────────────────────────────────────────────────┘
    ///                ╱ ╲
    ///               b  ┌───┐
    ///                  │ z │
    ///                  └───┘
    ///                   ╱ ╲
    ///                  c   d
    /// ```
    fn balance(self) -> Node<K, V> {
        use self::Color::Red as R;
        use self::Color::Black as B;

        match self.color {
            B => {
                let color_l:   Option<Color> = self.left_color();
                let color_l_l: Option<Color> = self.left.as_ref().and_then(|l| l.left_color());
                let color_l_r: Option<Color> = self.left.as_ref().and_then(|l| l.right_color());
                let color_r:   Option<Color> = self.right_color();
                let color_r_l: Option<Color> = self.right.as_ref().and_then(|r| r.left_color());
                let color_r_r: Option<Color> = self.right.as_ref().and_then(|r| r.right_color());

                match (color_l, color_l_l, color_l_r, color_r, color_r_l, color_r_r) {
                    // Case 1
                    (Some(R), Some(R), ..) => {
                        let node_l:   Arc<Node<K, V>> = self.left.unwrap();
                        let node_l_l: Arc<Node<K, V>> = node_l.left.clone().unwrap();

                        let tree_l_l_l: Option<Arc<Node<K, V>>> = node_l_l.left.clone();
                        let tree_l_l_r: Option<Arc<Node<K, V>>> = node_l_l.right.clone();
                        let tree_l_r:   Option<Arc<Node<K, V>>> = node_l.right.clone();
                        let tree_r:     Option<Arc<Node<K, V>>> = self.right;

                        let new_left = Node {
                            entry: Arc::clone(&node_l_l.entry),
                            color: Color::Black,
                            left:  tree_l_l_l,
                            right: tree_l_l_r,
                        };
                        let new_right = Node {
                            entry: self.entry,
                            color: Color::Black,
                            left:  tree_l_r,
                            right: tree_r,
                        };

                        Node {
                            entry: Arc::clone(&node_l.entry),
                            color: Color::Red,
                            left:  Some(Arc::new(new_left)),
                            right: Some(Arc::new(new_right)),
                        }
                    },

                    // Case 2
                    (Some(R), _, Some(R), ..) => {
                        let node_l:   Arc<Node<K, V>> = self.left.unwrap();
                        let node_l_r: Arc<Node<K, V>> = node_l.right.clone().unwrap();

                        let tree_l_l:   Option<Arc<Node<K, V>>> = node_l.left.clone();
                        let tree_l_r_l: Option<Arc<Node<K, V>>> = node_l_r.left.clone();
                        let tree_l_r_r: Option<Arc<Node<K, V>>> = node_l_r.right.clone();
                        let tree_r:     Option<Arc<Node<K, V>>> = self.right;

                        let new_left = Node {
                            entry: Arc::clone(&node_l.entry),
                            color: Color::Black,
                            left:  tree_l_l,
                            right: tree_l_r_l,
                        };
                        let new_right = Node {
                            entry: self.entry,
                            color: Color::Black,
                            left:  tree_l_r_r,
                            right: tree_r,
                        };

                        Node {
                            entry: Arc::clone(&node_l_r.entry),
                            color: Color::Red,
                            left:  Some(Arc::new(new_left)),
                            right: Some(Arc::new(new_right)),
                        }
                    },

                    // Case 3
                    (.., Some(R), Some(R), _) => {
                        let node_r:   Arc<Node<K, V>> = self.right.unwrap();
                        let node_r_l: Arc<Node<K, V>> = node_r.left.clone().unwrap();

                        let tree_l:     Option<Arc<Node<K, V>>> = self.left;
                        let tree_r_l_l: Option<Arc<Node<K, V>>> = node_r_l.left.clone();
                        let tree_r_l_r: Option<Arc<Node<K, V>>> = node_r_l.right.clone();
                        let tree_r_r:   Option<Arc<Node<K, V>>> = node_r.right.clone();

                        let new_left = Node {
                            entry: self.entry,
                            color: Color::Black,
                            left:  tree_l,
                            right: tree_r_l_l,
                        };
                        let new_right = Node {
                            entry: Arc::clone(&node_r.entry),
                            color: Color::Black,
                            left:  tree_r_l_r,
                            right: tree_r_r,
                        };

                        Node {
                            entry: Arc::clone(&node_r_l.entry),
                            color: Color::Red,
                            left:  Some(Arc::new(new_left)),
                            right: Some(Arc::new(new_right)),
                        }
                    },

                    // Case 4
                    (.., Some(R), _, Some(R)) => {
                        let node_r:   Arc<Node<K, V>> = self.right.unwrap();
                        let node_r_r: Arc<Node<K, V>> = node_r.right.clone().unwrap();

                        let tree_l:     Option<Arc<Node<K, V>>> = self.left;
                        let tree_r_l:   Option<Arc<Node<K, V>>> = node_r.left.clone();
                        let tree_r_r_l: Option<Arc<Node<K, V>>> = node_r_r.left.clone();
                        let tree_r_r_r: Option<Arc<Node<K, V>>> = node_r_r.right.clone();

                        let new_left = Node {
                            entry: self.entry,
                            color: Color::Black,
                            left:  tree_l,
                            right: tree_r_l,
                        };
                        let new_right = Node {
                            entry: Arc::clone(&node_r_r.entry),
                            color: Color::Black,
                            left:  tree_r_r_l,
                            right: tree_r_r_r,
                        };

                        Node {
                            entry: Arc::clone(&node_r.entry),
                            color: Color::Red,
                            left:  Some(Arc::new(new_left)),
                            right: Some(Arc::new(new_right)),
                        }
                    },

                    _ => self,
                }
            },
            R => self,
        }
    }

    /// Returns a pair with the node with the new entry and whether the key is new.
    fn insert(root: Option<&Node<K, V>>, key: K, value: V) -> (Node<K, V>, bool) {
        fn ins<K: Ord, V>(node: Option<&Node<K, V>>, k: K, v: V) -> (Node<K, V>, bool) {
            match node {
                Some(node) => {
                    match k.cmp(&node.entry.key) {
                        Ordering::Less => {
                            let left = Node::borrow(&node.left);
                            let (new_left, is_new_key) = ins(left, k, v);
                            let unbalanced_new_node = node.with_left(new_left);

                            // Small optimization: avoid unnecessary calls to balance.
                            let new_node = match is_new_key {
                                true  => unbalanced_new_node.balance(),
                                false => unbalanced_new_node,
                            };

                            (new_node, is_new_key)
                        },
                        Ordering::Equal => {
                            let new_node = node.with_entry(Entry::new(k, v));

                            (new_node, false)
                        },
                        Ordering::Greater => {
                            let right = Node::borrow(&node.right);
                            let (new_right, is_new_key) = ins(right, k, v);
                            let unbalanced_new_node = node.with_right(new_right);

                            // Small optimization: avoid unnecessary calls to balance.
                            let new_node = match is_new_key {
                                true  => unbalanced_new_node.balance(),
                                false => unbalanced_new_node,
                            };

                            (new_node, is_new_key)
                        },
                    }
                },
                None => {
                    let new_node = Node::new_red(Entry::new(k, v));

                    (new_node, true)
                },
            }
        }

        let (new_root, is_new_key) = ins(root, key, value);
        let new_root = new_root.make_black();

        (new_root, is_new_key)
    }

    /// Returns a pair with the node without the entry matching `key` and whether the key was present.
    ///
    /// If the node becomes empty it will return `None` in the first component of the pair.
    fn remove<Q: ?Sized>(root: Option<&Node<K, V>>, key: &Q) -> (Option<Node<K, V>>, bool)
        where K: Borrow<Q>,
              Q: Ord {
        fn fuse<K, V>(left: Option<&Node<K, V>>, right: Option<&Node<K, V>>) -> Option<Node<K, V>>
            where K: Ord {
            use self::Color::Red as R;
            use self::Color::Black as B;

            match (left, right) {
                (None, r) => r.map(Node::clone),
                (l, None) => l.map(Node::clone),
                (Some(l), Some(r)) => {
                    let tree_l_r = Node::borrow(&l.right);
                    let tree_r_l = Node::borrow(&r.left);

                    let new_node = match (l.color, r.color) {
                        (B, R) => {
                            let new_left = fuse(Some(l), tree_r_l);
                            Node {
                                entry: Arc::clone(&r.entry),
                                color: Color::Red,
                                left:  new_left.map(Arc::new),
                                right: r.right.clone(),
                            }
                        },
                        (R, B) => {
                            let new_right = fuse(tree_l_r, Some(r));
                            Node {
                                entry: Arc::clone(&l.entry),
                                color: Color::Red,
                                left:  l.left.clone(),
                                right: new_right.map(Arc::new),
                            }
                        },
                        (R, R) => {
                            let fused = fuse(tree_l_r, tree_r_l);

                            match fused {
                                Some(Node {color: R, entry: f_entry, left: f_left, right: f_right } ) => {
                                    let left_child = Node {
                                        entry: Arc::clone(&l.entry),
                                        color: Color::Red,
                                        left:  l.left.clone(),
                                        right: f_left,
                                    };
                                    let right_child = Node {
                                        entry: Arc::clone(&r.entry),
                                        color: Color::Red,
                                        left:  f_right,
                                        right: r.right.clone(),
                                    };

                                    Node {
                                        entry: f_entry,
                                        color: Color::Red,
                                        left:  Some(Arc::new(left_child)),
                                        right: Some(Arc::new(right_child)),
                                    }
                                },
                                fused => Node {
                                    entry: Arc::clone(&l.entry),
                                    color: Color::Red,
                                    left:  l.left.clone(),
                                    right: Some(Arc::new(
                                        Node {
                                            entry: Arc::clone(&r.entry),
                                            color: Color::Red,
                                            left:  fused.map(Arc::new),
                                            right: r.right.clone(),
                                        }
                                    )),
                                },
                            }
                        },
                        (B, B) => {
                            let fused = fuse(tree_l_r, tree_r_l);

                            match fused {
                                Some(Node {color: R, entry: f_entry, left: f_left, right: f_right } ) => {
                                    let left_child = Node {
                                        entry: Arc::clone(&l.entry),
                                        color: Color::Black,
                                        left:  l.left.clone(),
                                        right: f_left,
                                    };
                                    let right_child = Node {
                                        entry: Arc::clone(&r.entry),
                                        color: Color::Black,
                                        left:  f_right,
                                        right: r.right.clone(),
                                    };

                                    Node {
                                        entry: f_entry,
                                        color: Color::Red,
                                        left:  Some(Arc::new(left_child)),
                                        right: Some(Arc::new(right_child)),
                                    }
                                },
                                fused => {
                                    let new_node = Node {
                                        entry: Arc::clone(&l.entry),
                                        color: Color::Red,
                                        left:  l.left.clone(),
                                        right: Some(Arc::new(
                                            Node {
                                                entry: Arc::clone(&r.entry),
                                                color: Color::Black,
                                                left:  fused.map(Arc::new),
                                                right: r.right.clone(),
                                            }
                                        )),
                                    };

                                    balance_left(new_node)
                                },
                            }
                        },
                    };

                    Some(new_node)
                },
            }
        }

        fn balance<K, V>(node: Node<K, V>) -> Node<K, V>
            where K: Ord {
            match (node.left_color(), node.right_color()) {
                (Some(Color::Red), Some(Color::Red)) => {
                    let new_left = node.left
                        .map(|l| Arc::new(Node::clone(l.borrow()).make_black()));
                    let new_right = node.right
                        .map(|r| Arc::new(Node::clone(r.borrow()).make_black()));
                    Node {
                        entry: Arc::clone(&node.entry),
                        color: Color::Red,
                        left:  new_left,
                        right: new_right,
                    }
                },
                _ => {
                    // Our `balance()` does nothing unless the color is red, which the caller
                    // must ensure.
                    debug_assert!(node.color == Color::Black);
                    node.balance()
                },
            }
        }

        fn balance_left<K, V>(node: Node<K, V>) -> Node<K, V>
            where K: Ord {
            use self::Color::Red as R;
            use self::Color::Black as B;

            let color_l:   Option<Color> = node.left_color();
            let color_r:   Option<Color> = node.right_color();
            let color_r_l: Option<Color> = node.right.as_ref().and_then(|r| r.left_color());

            let tree_l = Node::borrow(&node.left);
            let tree_r = Node::borrow(&node.right);

            match (color_l, color_r, color_r_l) {
                (Some(R), ..) => {
                    let left = tree_l.unwrap();

                    Node {
                        entry: Arc::clone(&node.entry),
                        color: Color::Red,
                        left: Some(Arc::new(Node {
                            entry: Arc::clone(&left.entry),
                            color: Color::Black,
                            left:  left.left.clone(),
                            right: left.right.clone(),
                        })),
                        right: node.right.clone(),
                    }
                },
                (_, Some(B), _) => {
                    let right = tree_r.unwrap();

                    let new_node = Node {
                        entry: Arc::clone(&node.entry),
                        color: Color::Black,
                        left:  node.left.clone(),
                        right: Some(Arc::new(Node {
                            entry: Arc::clone(&right.entry),
                            color: Color::Red,
                            left:  right.left.clone(),
                            right: right.right.clone(),
                        })),
                    };

                    balance(new_node)
                },
                (_, Some(R), Some(B)) => {
                    let right = tree_r.unwrap();
                    let right_left = Node::borrow(&right.left).unwrap();

                    let unbalanced_new_right = Node {
                        entry: Arc::clone(&right.entry),
                        color: Color::Black,
                        left:  right_left.right.clone(),
                        right: Some(Arc::new(
                            Node::borrow(&right.right).unwrap().clone().make_red()
                        )),
                    };

                    let new_right = balance(unbalanced_new_right);

                    Node {
                        entry: Arc::clone(&right_left.entry),
                        color: Color::Red,
                        left: Some(Arc::new(Node {
                            entry: Arc::clone(&node.entry),
                            color: Color::Black,
                            left:  node.left.clone(),
                            right: right_left.left.clone(),
                        })),
                        right: Some(Arc::new(new_right)),
                    }
                },
                _ => unreachable!(),
            }
        }

        fn balance_right<K, V>(node: Node<K, V>) -> Node<K, V>
            where K: Ord {
            use self::Color::Red as R;
            use self::Color::Black as B;

            let color_r:   Option<Color> = node.right_color();
            let color_l:   Option<Color> = node.left_color();
            let color_l_r: Option<Color> = node.left.as_ref().and_then(|l| l.right_color());

            let tree_l = Node::borrow(&node.left);
            let tree_r = Node::borrow(&node.right);

            match (color_l, color_l_r, color_r) {
                (.., Some(R)) => {
                    let right = tree_r.unwrap();

                    Node {
                        entry: Arc::clone(&node.entry),
                        color: Color::Red,
                        left: node.left.clone(),
                        right: Some(Arc::new(Node {
                            entry: Arc::clone(&right.entry),
                            color: Color::Black,
                            left:  right.left.clone(),
                            right: right.right.clone(),
                        })),
                    }
                },
                (Some(B), ..) => {
                    let left = tree_l.unwrap();

                    let new_node = Node {
                        entry: Arc::clone(&node.entry),
                        color: Color::Black,
                        left: Some(Arc::new(Node {
                            entry: Arc::clone(&left.entry),
                            color: Color::Red,
                            left:  left.left.clone(),
                            right: left.right.clone(),
                        })),
                        right: node.right.clone(),
                    };

                    balance(new_node)
                },
                (Some(R), Some(B), _) => {
                    let left = tree_l.unwrap();
                    let left_right = Node::borrow(&left.right).unwrap();

                    let unbalanced_new_left = Node {
                        entry: Arc::clone(&left.entry),
                        color: Color::Black,
                        left: Some(Arc::new(
                            Node::borrow(&left.left).unwrap().clone().make_red()
                        )),
                        right: left_right.left.clone(),
                    };

                    let new_left = balance(unbalanced_new_left);

                    Node {
                        entry: Arc::clone(&left_right.entry),
                        color: Color::Red,
                        left: Some(Arc::new(new_left)),
                        right: Some(Arc::new(Node {
                            entry: Arc::clone(&node.entry),
                            color: Color::Black,
                            left:  left_right.right.clone(),
                            right: node.right.clone(),
                        })),
                    }
                },
                _ => unreachable!(),
            }
        }

        fn del_left<K, V, Q: ?Sized>(node: &Node<K, V>, k: &Q) -> (Option<Node<K, V>>, bool)
            where K: Borrow<Q> + Ord,
                  Q: Ord {
            let (new_left, removed) = del(Node::borrow(&node.left), k);
            let new_node = Node {
                entry: Arc::clone(&node.entry),
                color: Color::Red, // In case of rebalance the color does not matter.
                left:  new_left.map(Arc::new),
                right: node.right.clone(),
            };

            let balanced_new_node = match node.left_color() {
                Some(Color::Black) => balance_left(new_node),
                _ => new_node,
            };

            (Some(balanced_new_node), removed)
        }

        fn del_right<K, V, Q: ?Sized>(node: &Node<K, V>, k: &Q) -> (Option<Node<K, V>>, bool)
            where K: Borrow<Q> + Ord,
                  Q: Ord {
            let (new_right, removed) = del(Node::borrow(&node.right), k);
            let new_node = Node {
                entry: Arc::clone(&node.entry),
                color: Color::Red, // In case of rebalance the color does not matter.
                left:  node.left.clone(),
                right: new_right.map(Arc::new),
            };

            let balanced_new_node = match node.right_color() {
                Some(Color::Black) => balance_right(new_node),
                _ => new_node,
            };

            (Some(balanced_new_node), removed)
        }

        fn del<K, V, Q: ?Sized>(node: Option<&Node<K, V>>, k: &Q) -> (Option<Node<K, V>>, bool)
            where K: Borrow<Q> + Ord,
                  Q: Ord {
            match node {
                Some(node) => {
                    match k.cmp(node.entry.key.borrow()) {
                        Ordering::Less => del_left(node, k),
                        Ordering::Equal => {
                            let left = Node::borrow(&node.left);
                            let right = Node::borrow(&node.right);
                            let new_node = fuse(left, right);

                            (new_node, true)
                        },
                        Ordering::Greater => del_right(node, k),
                    }
                },
                None => (None, false),
            }
        }

        let (new_root, removed) = del(root, key);
        let new_root = new_root.map(|r| r.make_black());

        (new_root, removed)
    }
}

impl<K, V> RedBlackTreeMap<K, V>
    where K: Ord {
    pub fn new() -> RedBlackTreeMap<K, V> {
        RedBlackTreeMap {
            root: None,
            size: 0,
        }
    }

    pub fn get<Q: ?Sized>(&self, key: &Q) -> Option<&V>
        where K: Borrow<Q>,
              Q: Ord {
        self.root.as_ref()
            .and_then(|r| r.get(key))
            .map(|e| &e.value)
    }

    pub fn first(&self) -> Option<(&K, &V)> {
        self.root.as_ref()
            .map(|r| r.first())
            .map(|e| (&e.key, &e.value))
    }

    pub fn last(&self) -> Option<(&K, &V)> {
        self.root.as_ref()
            .map(|r| r.last())
            .map(|e| (&e.key, &e.value))
    }

    pub fn insert(&self, key: K, value: V) -> RedBlackTreeMap<K, V> {
        let root = Node::borrow(&self.root);
        let (new_root, is_new_key) = Node::insert(root, key, value);

        RedBlackTreeMap {
            root: Some(Arc::new(new_root)),
            size: self.size + if is_new_key { 1 } else { 0 },
        }
    }

    pub fn remove<Q: ?Sized>(&self, key: &Q) -> RedBlackTreeMap<K, V>
        where K: Borrow<Q>,
              Q: Ord {
        let root = Node::borrow(&self.root);
        let (new_root, removed) = Node::remove(root, key);

        // We want to keep maximum sharing so in case of no change we just `clone()` ourselves.
        if removed {
            RedBlackTreeMap {
                root: new_root.map(Arc::new),
                size: self.size - 1,
            }
        } else {
            self.clone()
        }
    }

    pub fn contains_key<Q: ?Sized>(&self, key: &Q) -> bool
        where K: Borrow<Q>,
              Q: Ord {
        self.get(key).is_some()
    }

    #[inline]
    pub fn size(&self) -> usize {
        self.size
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.size() == 0
    }

    pub fn iter(&self) -> Iter<K, V> {
        Iter::new(self)
    }

    pub fn keys(&self) -> IterKeys<K, V> {
        self.iter().map(|(k, _)| k)
    }

    pub fn values(&self) -> IterValues<K, V> {
        self.iter().map(|(_, v)| v)
    }
}

impl<'a, K, Q: ?Sized, V> Index<&'a Q> for RedBlackTreeMap<K, V>
    where K: Ord + Borrow<Q>,
          Q: Ord {
    type Output = V;

    fn index(&self, key: &Q) -> &V {
        self.get(key)
            .expect("no entry found for key")
    }
}

impl<K, V> Clone for RedBlackTreeMap<K, V>
    where K: Ord {
    fn clone(&self) -> RedBlackTreeMap<K, V> {
        RedBlackTreeMap {
            root: self.root.clone(),
            size: self.size,
        }
    }
}

impl<K, V> Default for RedBlackTreeMap<K, V>
    where K: Ord {
    fn default() -> RedBlackTreeMap<K, V> {
        RedBlackTreeMap::new()
    }
}

impl<K, V: PartialEq> PartialEq for RedBlackTreeMap<K, V>
    where K: Ord {
    fn eq(&self, other: &RedBlackTreeMap<K, V>) -> bool {
        self.size() == other.size() && self.iter().all(|(key, value)|
            other.get(key).map_or(false, |v| *value == *v)
        )
    }
}

impl<K, V: Eq> Eq for RedBlackTreeMap<K, V>
    where K: Ord {}

impl<K: Ord, V: PartialOrd> PartialOrd for RedBlackTreeMap<K, V> {
    fn partial_cmp(&self, other: &RedBlackTreeMap<K, V>) -> Option<Ordering> {
        self.iter().partial_cmp(other.iter())
    }
}

impl<K: Ord, V: Ord> Ord for RedBlackTreeMap<K, V> {
    fn cmp(&self, other: &RedBlackTreeMap<K, V>) -> Ordering {
        self.iter().cmp(other.iter())
    }
}

impl<K: Hash, V: Hash> Hash for RedBlackTreeMap<K, V>
    where K: Ord {
    fn hash<H: Hasher>(&self, state: &mut H) -> () {
        // Add the hash of length so that if two collections are added one after the other it doesn't
        // hash to the same thing as a single collection with the same elements in the same order.
        self.size().hash(state);

        for e in self {
            e.hash(state);
        }
    }
}

impl<K, V> Display for RedBlackTreeMap<K, V>
    where K: Ord + Display,
          V: Display {
    fn fmt(&self, fmt: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        let mut first = true;

        fmt.write_str("{")?;

        for (k, v) in self.iter() {
            if !first {
                fmt.write_str(", ")?;
            }
            k.fmt(fmt)?;
            fmt.write_str(": ")?;
            v.fmt(fmt)?;
            first = false;
        }

        fmt.write_str("}")
    }
}

impl<'a, K, V> IntoIterator for &'a RedBlackTreeMap<K, V>
    where K: Ord {
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;

    fn into_iter(self) -> Iter<'a, K, V> {
        self.iter()
    }
}

// TODO This can be improved to create a perfectly balanced tree.
impl<K, V> FromIterator<(K, V)> for RedBlackTreeMap<K, V> where
    K: Ord {
    fn from_iter<I: IntoIterator<Item = (K, V)>>(into_iter: I) -> RedBlackTreeMap<K, V> {
        let mut map = RedBlackTreeMap::new();

        for (k, v) in into_iter {
            map = map.insert(k, v);
        }

        map
    }
}

#[derive(Debug)]
pub struct Iter<'a, K: 'a, V: 'a> {
    map: &'a RedBlackTreeMap<K, V>,

    stack_forward:  Option<Vec<&'a Node<K, V>>>,
    stack_backward: Option<Vec<&'a Node<K, V>>>,

    left_index:  usize, // inclusive
    right_index: usize, // exclusive
}

mod iter_utils {
    use std::mem::size_of;

    pub fn lg_floor(size: usize) -> usize {
        debug_assert!(size > 0);

        let c: usize = 8 * size_of::<usize>() - size.leading_zeros() as usize;

        c - 1
    }

    pub fn pessimistic_height(size: usize) -> usize {
        if size > 0 {
            2 * lg_floor(size + 1)
        } else {
            0
        }
    }
}

impl<'a, K, V> Iter<'a, K, V>
    where K: Ord {
    fn new(map: &RedBlackTreeMap<K, V>) -> Iter<K, V> {
        Iter {
            map,

            stack_forward:  None,
            stack_backward: None,

            left_index: 0,
            right_index: map.size(),
        }
    }

    fn dig(stack: &mut Vec<&Node<K, V>>, backwards: bool) -> () {
        let child =
            stack
                .last()
                .and_then(|node| {
                    let c = if backwards { &node.right } else { &node.left };
                    Node::borrow(c)
                });

        if let Some(c) = child {
            stack.push(c);
            Iter::dig(stack, backwards);
        }
    }

    fn init_if_needed(&mut self, backwards: bool) -> () {
        let stack_field = if backwards {
            &mut self.stack_backward
        } else {
            &mut self.stack_forward
        };

        if stack_field.is_none() {
            let mut stack =
                Vec::with_capacity(iter_utils::pessimistic_height(self.map.size()) + 1);

            // TODO Use foreach when stable.
            Node::borrow(&self.map.root).map(|r| stack.push(r));

            Iter::dig(&mut stack, backwards);

            *stack_field = Some(stack);
        }
    }

    #[inline]
    fn non_empty(&self) -> bool {
        self.left_index < self.right_index
    }

    fn advance(stack: &mut Vec<&Node<K, V>>, backwards: bool) -> () {
        match stack.pop() {
            Some(node) => {
                let child = if backwards { &node.left } else { &node.right };

                if let Some(c) = Node::borrow(child) {
                    stack.push(c);
                    Iter::dig(stack, backwards);
                }
            },
            None => (), // Reached the end.  Nothing to do.
        }
    }

    #[inline]
    fn current(stack: &[&'a Node<K, V>]) -> Option<(&'a K, &'a V)> {
        stack.last().map(|node| (&node.entry.key, &node.entry.value))
    }

    fn advance_forward(&mut self) -> () {
        if self.non_empty() {
            Iter::advance(&mut self.stack_forward.as_mut().unwrap(), false);

            self.left_index += 1;
        }
    }

    fn current_forward(&mut self) -> Option<(&'a K, &'a V)> {
        if self.non_empty() {
            Iter::current(self.stack_forward.as_ref().unwrap())
        } else {
            None
        }
    }

    fn advance_backward(&mut self) -> () {
        if self.non_empty() {
            Iter::advance(&mut self.stack_backward.as_mut().unwrap(), true);

            self.right_index -= 1;
        }
    }

    fn current_backward(&mut self) -> Option<(&'a K, &'a V)> {
        if self.non_empty() {
            Iter::current(self.stack_backward.as_ref().unwrap())
        } else {
            None
        }
    }
}

impl<'a, K, V> Iterator for Iter<'a, K, V>
    where K: Ord {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<(&'a K, &'a V)> {
        self.init_if_needed(false);

        let current = self.current_forward();

        self.advance_forward();

        current
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.right_index - self.left_index;

        (len, Some(len))
    }
}

impl<'a, K, V> DoubleEndedIterator for Iter<'a, K, V>
    where K: Ord {
    fn next_back(&mut self) -> Option<(&'a K, &'a V)> {
        self.init_if_needed(true);

        let current = self.current_backward();

        self.advance_backward();

        current
    }
}

impl<'a, K: Ord, V> ExactSizeIterator for Iter<'a, K, V> {}

#[cfg(feature = "serde")]
pub mod serde {
    use super::*;
    use serde::ser::{Serialize, Serializer};
    use serde::de::{Deserialize, Deserializer, MapAccess, Visitor};
    use std::marker::PhantomData;
    use std::fmt;

    impl<K, V> Serialize for RedBlackTreeMap<K, V>
        where K: Ord + Serialize,
              V: Serialize {
        fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
            serializer.collect_map(self)
        }
    }

    impl<'de, K, V> Deserialize<'de> for RedBlackTreeMap<K, V>
        where K: Ord + Deserialize<'de>,
              V: Deserialize<'de> {
        fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<RedBlackTreeMap<K, V>, D::Error> {
            deserializer.deserialize_map(RedBlackTreeMapVisitor { phantom: PhantomData } )
        }
    }

    struct RedBlackTreeMapVisitor<K, V> {
        phantom: PhantomData<(K, V)>
    }

    impl<'de, K, V> Visitor<'de> for RedBlackTreeMapVisitor<K, V>
        where K: Ord + Deserialize<'de>,
              V: Deserialize<'de> {
        type Value = RedBlackTreeMap<K, V>;

        fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
            formatter.write_str("a map")
        }

        fn visit_map<A>(self, mut map: A) -> Result<RedBlackTreeMap<K, V>, A::Error>
            where A: MapAccess<'de> {
            let mut rbtreemap = RedBlackTreeMap::new();

            while let Some((k, v)) = map.next_entry()? {
                rbtreemap = rbtreemap.insert(k, v);
            }

            Ok(rbtreemap)
        }
    }
}

#[cfg(test)]
mod test;
