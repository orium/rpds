/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use super::entry::Entry;
use std::borrow::Borrow;
use std::cmp::Ordering;
use std::fmt::Display;
use std::hash::{Hash, Hasher};
use std::iter::FromIterator;
use std::marker::PhantomData;
use std::ops::{Index, RangeBounds, RangeFull};
use std::sync::Arc;

// TODO Use impl trait instead of this when available.
pub type Iter<'a, K, V> =
    std::iter::Map<IterArc<'a, K, V>, fn(&'a Arc<Entry<K, V>>) -> (&'a K, &'a V)>;
pub type IterKeys<'a, K, V> = std::iter::Map<Iter<'a, K, V>, fn((&'a K, &V)) -> &'a K>;
pub type IterValues<'a, K, V> = std::iter::Map<Iter<'a, K, V>, fn((&K, &'a V)) -> &'a V>;
pub type RangeIter<'a, K, V, RB, Q> =
    std::iter::Map<RangeIterArc<'a, K, V, RB, Q>, fn(&'a Arc<Entry<K, V>>) -> (&'a K, &'a V)>;

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
                m.insert_mut($k, $v);
            )*
            m
        }
    };
}

/// A persistent map with structural sharing.  This implementation uses a
/// [red-black tree](https://en.wikipedia.org/wiki/Red-Black_tree).
///
/// # Complexity
///
/// Let *n* be the number of elements in the map.
///
/// ## Temporal complexity
///
/// | Operation                  | Average   | Worst case  |
/// |:-------------------------- | ---------:| -----------:|
/// | `new()`                    |      Θ(1) |        Θ(1) |
/// | `insert()`                 | Θ(log(n)) |   Θ(log(n)) |
/// | `remove()`                 | Θ(log(n)) |   Θ(log(n)) |
/// | `get()`                    | Θ(log(n)) |   Θ(log(n)) |
/// | `contains_key()`           | Θ(log(n)) |   Θ(log(n)) |
/// | `size()`                   |      Θ(1) |        Θ(1) |
/// | `clone()`                  |      Θ(1) |        Θ(1) |
/// | iterator creation          | Θ(log(n)) |   Θ(log(n)) |
/// | iterator step              |      Θ(1) |   Θ(log(n)) |
/// | iterator full              |      Θ(n) |        Θ(n) |
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
    left: Option<Arc<Node<K, V>>>,
    right: Option<Arc<Node<K, V>>>,
}

impl<K, V> Clone for Node<K, V> {
    fn clone(&self) -> Node<K, V> {
        Node {
            entry: Arc::clone(&self.entry),
            color: self.color,
            left: self.left.clone(),
            right: self.right.clone(),
        }
    }
}

impl<K, V> Node<K, V>
where
    K: Ord,
{
    fn new_red(entry: Entry<K, V>) -> Node<K, V> {
        Node {
            entry: Arc::new(entry),
            color: Color::Red,
            left: None,
            right: None,
        }
    }

    fn new_black(entry: Entry<K, V>) -> Node<K, V> {
        Node {
            entry: Arc::new(entry),
            color: Color::Black,
            left: None,
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

    fn get<Q: ?Sized>(&self, key: &Q) -> Option<&Entry<K, V>>
    where
        K: Borrow<Q>,
        Q: Ord,
    {
        match key.cmp(self.entry.key.borrow()) {
            Ordering::Less => self.left.as_ref().and_then(|l| l.get(key)),
            Ordering::Equal => Some(&self.entry),
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
    fn balance(&mut self) {
        use std::mem::swap;
        use Color::Black as B;
        use Color::Red as R;

        match self.color {
            B => {
                let color_l: Option<Color> = self.left_color();
                let color_l_l: Option<Color> = self.left.as_ref().and_then(|l| l.left_color());
                let color_l_r: Option<Color> = self.left.as_ref().and_then(|l| l.right_color());
                let color_r: Option<Color> = self.right_color();
                let color_r_l: Option<Color> = self.right.as_ref().and_then(|r| r.left_color());
                let color_r_r: Option<Color> = self.right.as_ref().and_then(|r| r.right_color());

                match (color_l, color_l_l, color_l_r, color_r, color_r_l, color_r_r) {
                    // Case 1
                    (Some(R), Some(R), ..) => {
                        let mut node_l_arc = self.left.take().unwrap();
                        let node_l: &mut Node<K, V> = Arc::make_mut(&mut node_l_arc);
                        let mut node_l_l_arc = node_l.left.take().unwrap();
                        let node_l_l: &mut Node<K, V> = Arc::make_mut(&mut node_l_l_arc);

                        self.color = Color::Red;
                        node_l.color = Color::Black;
                        node_l_l.color = Color::Black;

                        swap(&mut self.entry, &mut node_l.entry);
                        swap(&mut node_l.left, &mut node_l.right);
                        swap(&mut self.right, &mut node_l.right);

                        self.left = Some(node_l_l_arc);
                        self.right = Some(node_l_arc);
                    }

                    // Case 2
                    (Some(R), _, Some(R), ..) => {
                        let mut node_l_arc = self.left.take().unwrap();
                        let node_l: &mut Node<K, V> = Arc::make_mut(&mut node_l_arc);
                        let mut node_l_r_arc = node_l.right.take().unwrap();
                        let node_l_r: &mut Node<K, V> = Arc::make_mut(&mut node_l_r_arc);

                        self.color = Color::Red;
                        node_l.color = Color::Black;
                        node_l_r.color = Color::Black;

                        swap(&mut self.entry, &mut node_l_r.entry);
                        swap(&mut node_l_r.left, &mut node_l_r.right);
                        swap(&mut node_l.right, &mut node_l_r.right);
                        swap(&mut self.right, &mut node_l_r.right);

                        self.right = Some(node_l_r_arc);
                        self.left = Some(node_l_arc);
                    }

                    // Case 3
                    (.., Some(R), Some(R), _) => {
                        let mut node_r_arc = self.right.take().unwrap();
                        let node_r: &mut Node<K, V> = Arc::make_mut(&mut node_r_arc);
                        let mut node_r_l_arc = node_r.left.take().unwrap();
                        let node_r_l: &mut Node<K, V> = Arc::make_mut(&mut node_r_l_arc);

                        self.color = Color::Red;
                        node_r.color = Color::Black;
                        node_r_l.color = Color::Black;

                        swap(&mut self.entry, &mut node_r_l.entry);
                        swap(&mut node_r.left, &mut node_r_l.right);
                        swap(&mut node_r_l.left, &mut node_r_l.right);
                        swap(&mut self.left, &mut node_r_l.left);

                        self.left = Some(node_r_l_arc);
                        self.right = Some(node_r_arc);
                    }

                    // Case 4
                    (.., Some(R), _, Some(R)) => {
                        let mut node_r_arc = self.right.take().unwrap();
                        let node_r: &mut Node<K, V> = Arc::make_mut(&mut node_r_arc);
                        let mut node_r_r_arc = node_r.right.take().unwrap();
                        let node_r_r: &mut Node<K, V> = Arc::make_mut(&mut node_r_r_arc);

                        self.color = Color::Red;
                        node_r.color = Color::Black;
                        node_r_r.color = Color::Black;

                        swap(&mut self.entry, &mut node_r.entry);
                        swap(&mut node_r.left, &mut node_r.right);
                        swap(&mut self.left, &mut node_r.left);

                        self.right = Some(node_r_r_arc);
                        self.left = Some(node_r_arc);
                    }

                    _ => (),
                }
            }
            R => (),
        }
    }

    /// Inserts the entry and returns whether the key is new.
    fn insert(root: &mut Option<Arc<Node<K, V>>>, key: K, value: V) -> bool {
        fn ins<K: Ord, V>(node: &mut Option<Arc<Node<K, V>>>, k: K, v: V, is_root: bool) -> bool {
            match node {
                Some(n) => {
                    let node = Arc::make_mut(n);

                    let ret = match k.cmp(&node.entry.key) {
                        Ordering::Less => {
                            let is_new_key = ins(&mut node.left, k, v, false);

                            // Small optimization: avoid unnecessary calls to balance.
                            if is_new_key {
                                node.balance();
                            }

                            is_new_key
                        }
                        Ordering::Equal => {
                            node.entry = Arc::new(Entry::new(k, v));

                            false
                        }
                        Ordering::Greater => {
                            let is_new_key = ins(&mut node.right, k, v, false);

                            // Small optimization: avoid unnecessary calls to balance.
                            if is_new_key {
                                node.balance();
                            }

                            is_new_key
                        }
                    };

                    if is_root {
                        node.color = Color::Black;
                    }

                    ret
                }
                None => {
                    *node = if is_root {
                        Some(Arc::new(Node::new_black(Entry::new(k, v))))
                    } else {
                        Some(Arc::new(Node::new_red(Entry::new(k, v))))
                    };

                    true
                }
            }
        }

        ins(root, key, value, true)
    }

    /// Returns `false` if node has no children to merge.
    fn remove_fuse(
        node: &mut Node<K, V>,
        left: Option<Arc<Node<K, V>>>,
        right: Option<Arc<Node<K, V>>>,
    ) -> bool {
        use Color::Black as B;
        use Color::Red as R;

        use std::mem::swap;

        match (left, right) {
            (None, None) => false,
            (None, Some(r_arc)) => {
                crate::utils::replace(node, r_arc);
                true
            }
            (Some(l_arc), None) => {
                crate::utils::replace(node, l_arc);
                true
            }
            (Some(mut l_arc), Some(mut r_arc)) => {
                match (l_arc.color, r_arc.color) {
                    (B, R) => {
                        let r = Arc::make_mut(&mut r_arc);
                        let rl = r.left.take();

                        // This will always return `true`.
                        Node::remove_fuse(node, Some(l_arc), rl);

                        swap(node, r);

                        node.left = Some(r_arc);
                    }
                    (R, B) => {
                        let l = Arc::make_mut(&mut l_arc);
                        let lr = l.right.take();

                        // This will always return `true`.
                        Node::remove_fuse(node, lr, Some(r_arc));

                        swap(node, l);

                        node.right = Some(l_arc);
                    }
                    (R, R) => {
                        let r = Arc::make_mut(&mut r_arc);
                        let rl = r.left.take();
                        let l = Arc::make_mut(&mut l_arc);
                        let lr = l.right.take();

                        let fused = Node::remove_fuse(node, lr, rl);

                        match node.color {
                            R if fused => {
                                let fl = node.left.take();
                                let fr = node.right.take();

                                l.right = fl;
                                r.left = fr;

                                node.left = Some(l_arc);
                                node.right = Some(r_arc);
                            }
                            _ => {
                                swap(l, node);

                                if fused {
                                    r.left = Some(l_arc);
                                }

                                node.right = Some(r_arc);
                            }
                        }
                    }
                    (B, B) => {
                        let r = Arc::make_mut(&mut r_arc);
                        let rl = r.left.take();
                        let l = Arc::make_mut(&mut l_arc);
                        let lr = l.right.take();

                        let fused = Node::remove_fuse(node, lr, rl);

                        match node.color {
                            R if fused => {
                                let fl = node.left.take();
                                let fr = node.right.take();

                                l.right = fl;
                                r.left = fr;

                                node.left = Some(l_arc);
                                node.right = Some(r_arc);
                            }
                            _ => {
                                swap(l, node);

                                if fused {
                                    r.left = Some(l_arc);
                                }

                                node.color = Color::Red;
                                node.right = Some(r_arc);

                                node.remove_balance_left();
                            }
                        }
                    }
                };

                true
            }
        }
    }

    fn remove_balance(&mut self) {
        match (self.left_color(), self.right_color()) {
            (Some(Color::Red), Some(Color::Red)) => {
                Arc::make_mut(self.left.as_mut().unwrap()).color = Color::Black;
                Arc::make_mut(self.right.as_mut().unwrap()).color = Color::Black;

                self.color = Color::Red;
            }
            _ => {
                // Our `balance()` does nothing unless the color is black, which the caller
                // must ensure.
                debug_assert_eq!(self.color, Color::Black);
                self.balance();
            }
        }
    }

    fn remove_balance_left(&mut self) {
        use Color::Black as B;
        use Color::Red as R;

        use std::mem::swap;

        let color_l: Option<Color> = self.left_color();
        let color_r: Option<Color> = self.right_color();
        let color_r_l: Option<Color> = self.right.as_ref().and_then(|r| r.left_color());

        match (color_l, color_r, color_r_l) {
            (Some(R), ..) => {
                let self_l = Arc::make_mut(self.left.as_mut().unwrap());

                self.color = Color::Red;
                self_l.color = Color::Black;
            }
            (_, Some(B), _) => {
                let self_r = Arc::make_mut(self.right.as_mut().unwrap());

                self.color = Color::Black;
                self_r.color = Color::Red;

                self.remove_balance();
            }
            (_, Some(R), Some(B)) => {
                let self_r = Arc::make_mut(self.right.as_mut().unwrap());

                let mut self_r_l_arc = self_r.left.take().unwrap();
                let self_r_l = Arc::make_mut(&mut self_r_l_arc);
                let new_r_l = self_r_l.right.take();

                self_r.color = Color::Black;
                self_r.left = new_r_l;
                Arc::make_mut(self_r.right.as_mut().unwrap()).color = Color::Red;

                self_r.remove_balance();

                self.color = Color::Red;

                self_r_l.right = self_r_l.left.take();
                self_r_l.left = self.left.take();

                swap(&mut self.entry, &mut self_r_l.entry);

                self.left = Some(self_r_l_arc);
            }
            _ => unreachable!(),
        }
    }

    fn remove_balance_right(&mut self) {
        use Color::Black as B;
        use Color::Red as R;

        use std::mem::swap;

        let color_r: Option<Color> = self.right_color();
        let color_l: Option<Color> = self.left_color();
        let color_l_r: Option<Color> = self.left.as_ref().and_then(|l| l.right_color());

        match (color_l, color_l_r, color_r) {
            (.., Some(R)) => {
                let self_r = Arc::make_mut(self.right.as_mut().unwrap());

                self.color = Color::Red;
                self_r.color = Color::Black;
            }
            (Some(B), ..) => {
                let self_l = Arc::make_mut(self.left.as_mut().unwrap());

                self.color = Color::Black;
                self_l.color = Color::Red;

                self.remove_balance();
            }
            (Some(R), Some(B), _) => {
                let self_l = Arc::make_mut(self.left.as_mut().unwrap());

                let mut self_l_r_arc = self_l.right.take().unwrap();
                let self_l_r = Arc::make_mut(&mut self_l_r_arc);
                let new_l_r = self_l_r.left.take();

                self_l.color = Color::Black;
                self_l.right = new_l_r;
                Arc::make_mut(self_l.left.as_mut().unwrap()).color = Color::Red;

                self_l.remove_balance();

                self.color = Color::Red;

                self_l_r.left = self_l_r.right.take();
                self_l_r.right = self.right.take();

                swap(&mut self.entry, &mut self_l_r.entry);

                self.right = Some(self_l_r_arc);
            }
            _ => unreachable!(),
        }
    }

    /// Returns `true` if the key was present.
    ///
    /// If the node becomes empty `*root` will be set to `None`.
    fn remove<Q: ?Sized>(root: &mut Option<Arc<Node<K, V>>>, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Ord,
    {
        fn del_left<K, V, Q: ?Sized>(node: &mut Node<K, V>, k: &Q) -> bool
        where
            K: Borrow<Q> + Ord,
            Q: Ord,
        {
            let original_left_color = node.left_color();
            let removed = del(&mut node.left, k, false);

            node.color = Color::Red; // In case of rebalance the color does not matter.

            if let Some(Color::Black) = original_left_color {
                node.remove_balance_left();
            }

            removed
        }

        fn del_right<K, V, Q: ?Sized>(node: &mut Node<K, V>, k: &Q) -> bool
        where
            K: Borrow<Q> + Ord,
            Q: Ord,
        {
            let original_right_color = node.right_color();

            let removed = del(&mut node.right, k, false);

            node.color = Color::Red; // In case of rebalance the color does not matter.

            if let Some(Color::Black) = original_right_color {
                node.remove_balance_right();
            }

            removed
        }

        fn del<K, V, Q: ?Sized>(node: &mut Option<Arc<Node<K, V>>>, k: &Q, is_root: bool) -> bool
        where
            K: Borrow<Q> + Ord,
            Q: Ord,
        {
            let (removed, make_node_none) = match *node {
                Some(ref mut node_arc) => {
                    let node = Arc::make_mut(node_arc);

                    let ret = match k.cmp(node.entry.key.borrow()) {
                        Ordering::Less => (del_left(node, k), false),
                        Ordering::Equal => {
                            let left = node.left.take();
                            let right = node.right.take();

                            let make_node_none = !Node::remove_fuse(node, left, right);

                            (true, make_node_none)
                        }
                        Ordering::Greater => (del_right(node, k), false),
                    };

                    if is_root {
                        node.color = Color::Black;
                    }

                    ret
                }
                None => (false, false),
            };

            if make_node_none {
                *node = None;
            }

            removed
        }

        del(root, key, true)
    }
}

impl<K, V> RedBlackTreeMap<K, V>
where
    K: Ord,
{
    #[must_use]
    pub fn new() -> RedBlackTreeMap<K, V> {
        RedBlackTreeMap {
            root: None,
            size: 0,
        }
    }

    #[must_use]
    pub fn get<Q: ?Sized>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Ord,
    {
        self.root
            .as_ref()
            .and_then(|r| r.get(key))
            .map(|e| &e.value)
    }

    #[must_use]
    pub fn first(&self) -> Option<(&K, &V)> {
        self.root
            .as_ref()
            .map(|r| r.first())
            .map(|e| (&e.key, &e.value))
    }

    #[must_use]
    pub fn last(&self) -> Option<(&K, &V)> {
        self.root
            .as_ref()
            .map(|r| r.last())
            .map(|e| (&e.key, &e.value))
    }

    #[must_use]
    pub fn insert(&self, key: K, value: V) -> RedBlackTreeMap<K, V> {
        let mut new_map = self.clone();

        new_map.insert_mut(key, value);

        new_map
    }

    pub fn insert_mut(&mut self, key: K, value: V) {
        let is_new_key = Node::insert(&mut self.root, key, value);

        if is_new_key {
            self.size += 1;
        }
    }

    #[must_use]
    pub fn remove<Q: ?Sized>(&self, key: &Q) -> RedBlackTreeMap<K, V>
    where
        K: Borrow<Q>,
        Q: Ord,
    {
        let mut new_map = self.clone();

        if new_map.remove_mut(key) {
            new_map
        } else {
            // We want to keep maximum sharing so in case of no change we just `clone()` ourselves.
            self.clone()
        }
    }

    pub fn remove_mut<Q: ?Sized>(&mut self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Ord,
    {
        let removed = Node::remove(&mut self.root, key);

        // Note that unfortunately, even if nothing was removed, we still might have cloned some
        // part of the tree unnecessarily.

        if removed {
            self.size -= 1;
        }

        removed
    }

    #[must_use]
    pub fn contains_key<Q: ?Sized>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Ord,
    {
        self.get(key).is_some()
    }

    #[must_use]
    #[inline]
    pub fn size(&self) -> usize {
        self.size
    }

    #[must_use]
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.size() == 0
    }

    #[must_use]
    pub fn iter(&self) -> Iter<'_, K, V> {
        self.iter_arc().map(|e| (&e.key, &e.value))
    }

    fn iter_arc(&self) -> IterArc<'_, K, V> {
        IterArc::new(self)
    }

    #[must_use]
    pub fn keys(&self) -> IterKeys<'_, K, V> {
        self.iter().map(|(k, _)| k)
    }

    #[must_use]
    pub fn values(&self) -> IterValues<'_, K, V> {
        self.iter().map(|(_, v)| v)
    }

    #[must_use]
    pub fn range<Q, RB>(&self, range: RB) -> RangeIter<'_, K, V, RB, Q>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
        RB: RangeBounds<Q>,
    {
        use std::ops::Bound::*;

        match (range.start_bound(), range.end_bound()) {
            (Excluded(s), Excluded(e)) if s == e => {
                panic!("range start and end are equal and excluded")
            }
            (Included(s), Included(e))
            | (Included(s), Excluded(e))
            | (Excluded(s), Included(e))
            | (Excluded(s), Excluded(e))
                if s > e =>
            {
                panic!("range start is greater than range end")
            }
            (_, _) => RangeIterArc::new(self, range).map(|e| (&e.key, &e.value)),
        }
    }
}

impl<'a, K, Q: ?Sized, V> Index<&'a Q> for RedBlackTreeMap<K, V>
where
    K: Ord + Borrow<Q>,
    Q: Ord,
{
    type Output = V;

    fn index(&self, key: &Q) -> &V {
        self.get(key).expect("no entry found for key")
    }
}

impl<K, V> Clone for RedBlackTreeMap<K, V>
where
    K: Ord,
{
    fn clone(&self) -> RedBlackTreeMap<K, V> {
        RedBlackTreeMap {
            root: self.root.clone(),
            size: self.size,
        }
    }
}

impl<K, V> Default for RedBlackTreeMap<K, V>
where
    K: Ord,
{
    fn default() -> RedBlackTreeMap<K, V> {
        RedBlackTreeMap::new()
    }
}

impl<K, V: PartialEq> PartialEq for RedBlackTreeMap<K, V>
where
    K: Ord,
{
    fn eq(&self, other: &RedBlackTreeMap<K, V>) -> bool {
        self.size() == other.size()
            && self
                .iter()
                .all(|(key, value)| other.get(key).map_or(false, |v| *value == *v))
    }
}

impl<K, V: Eq> Eq for RedBlackTreeMap<K, V> where K: Ord {}

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
where
    K: Ord,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Add the hash of length so that if two collections are added one after the other it
        // doesn't hash to the same thing as a single collection with the same elements in the same
        // order.
        self.size().hash(state);

        for e in self {
            e.hash(state);
        }
    }
}

impl<K, V> Display for RedBlackTreeMap<K, V>
where
    K: Ord + Display,
    V: Display,
{
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
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
where
    K: Ord,
{
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;

    fn into_iter(self) -> Iter<'a, K, V> {
        self.iter()
    }
}

// TODO This can be improved to create a perfectly balanced tree.
impl<K, V> FromIterator<(K, V)> for RedBlackTreeMap<K, V>
where
    K: Ord,
{
    fn from_iter<I: IntoIterator<Item = (K, V)>>(into_iter: I) -> RedBlackTreeMap<K, V> {
        let mut map = RedBlackTreeMap::new();

        for (k, v) in into_iter {
            map.insert_mut(k, v);
        }

        map
    }
}

mod iter_utils {
    use super::{Entry, Node, RedBlackTreeMap};
    use std::borrow::Borrow;
    use std::mem::size_of;
    use std::ops::Bound;
    use std::sync::Arc;

    // This is a stack for navigating through the tree. It can be used to go either forwards or
    // backwards: you choose the direction at construction time, and then every call to `advance`
    // goes in that direction.
    #[derive(Debug)]
    pub struct IterStack<'a, K, V> {
        // The invariant maintained by `stack` depends on whether we are moving forwards or backwards.
        // In either case, the current node is at the top of the stack. If we are moving forwards, the
        // rest of the stack consists of those ancestors of the current node that contain the current
        // node in their left subtree. In other words, the keys in the stack increase as we go from the
        // top of the stack to the bottom.
        stack: Vec<&'a Node<K, V>>,
        backwards: bool,
    }

    impl<'a, K, V> IterStack<'a, K, V>
    where
        K: Ord,
    {
        pub fn new<Q>(
            map: &'a RedBlackTreeMap<K, V>,
            start_bound: Bound<&Q>,
            end_bound: Bound<&Q>,
            backwards: bool,
        ) -> IterStack<'a, K, V>
        where
            K: Borrow<Q>,
            Q: Ord + ?Sized,
        {
            let size = conservative_height(map.size()) + 1;

            let mut stack = IterStack {
                stack: Vec::with_capacity(size),
                backwards,
            };

            if let Some(ref root) = map.root {
                stack.dig_towards(root.borrow(), start_bound, end_bound);
            }

            stack.clear_if_finished(start_bound, end_bound);

            stack
        }

        fn clear_if_finished<Q>(&mut self, start_bound: Bound<&Q>, end_bound: Bound<&Q>)
        where
            K: Borrow<Q>,
            Q: Ord + ?Sized,
        {
            use std::ops::Bound::*;

            if let Some(entry) = self.current() {
                let in_range = if self.backwards {
                    match start_bound {
                        Included(v) => entry.key.borrow() >= v,
                        Excluded(v) => entry.key.borrow() > v,
                        Unbounded => true,
                    }
                } else {
                    match end_bound {
                        Included(v) => entry.key.borrow() <= v,
                        Excluded(v) => entry.key.borrow() < v,
                        Unbounded => true,
                    }
                };

                if !in_range {
                    self.stack.clear();
                }
            };
        }

        #[inline]
        pub fn current(&self) -> Option<&'a Arc<Entry<K, V>>> {
            self.stack.last().map(|node| &node.entry)
        }

        fn dig<Q>(&mut self, start_bound: Bound<&Q>, end_bound: Bound<&Q>)
        where
            K: Borrow<Q>,
            Q: Ord + ?Sized,
        {
            let child = self.stack.last().and_then(|node| {
                let c = if self.backwards {
                    &node.right
                } else {
                    &node.left
                };
                Node::borrow(c)
            });

            if let Some(c) = child {
                self.stack.push(c);
                self.dig(start_bound, end_bound);
            }
        }

        fn dig_towards<Q>(
            &mut self,
            node: &'a Node<K, V>,
            start_bound: Bound<&Q>,
            end_bound: Bound<&Q>,
        ) where
            K: Borrow<Q>,
            Q: Ord + ?Sized,
        {
            use std::ops::Bound::*;

            let in_range = if self.backwards {
                match end_bound {
                    Included(v) => node.entry.key.borrow() <= v,
                    Excluded(v) => node.entry.key.borrow() < v,
                    Unbounded => true,
                }
            } else {
                match start_bound {
                    Included(v) => node.entry.key.borrow() >= v,
                    Excluded(v) => node.entry.key.borrow() > v,
                    Unbounded => true,
                }
            };

            if in_range {
                self.stack.push(node);
            }

            let child = match (self.backwards, in_range) {
                (false, true) => &node.left,
                (false, false) => &node.right,
                (true, true) => &node.right,
                (true, false) => &node.left,
            };

            if let Some(c) = child {
                self.dig_towards(c.borrow(), start_bound, end_bound);
            }
        }

        pub fn advance<Q>(&mut self, start_bound: Bound<&Q>, end_bound: Bound<&Q>)
        where
            K: Borrow<Q>,
            Q: Ord + ?Sized,
        {
            if let Some(node) = self.stack.pop() {
                let child = if self.backwards {
                    &node.left
                } else {
                    &node.right
                };

                if let Some(c) = Node::borrow(child) {
                    self.stack.push(c);
                    self.dig(start_bound, end_bound);
                }

                self.clear_if_finished(start_bound, end_bound);
            }
        }
    }

    pub fn lg_floor(size: usize) -> usize {
        debug_assert!(size > 0);

        let c: usize = 8 * size_of::<usize>() - size.leading_zeros() as usize;

        c - 1
    }

    pub fn conservative_height(size: usize) -> usize {
        if size > 0 {
            2 * lg_floor(size + 1)
        } else {
            0
        }
    }
}

#[derive(Debug)]
pub struct IterArc<'a, K, V> {
    range_iter: RangeIterArc<'a, K, V, RangeFull, K>,

    // Number of elements left in the iterator.
    size: usize,
}

impl<'a, K, V> IterArc<'a, K, V>
where
    K: Ord,
{
    fn new(map: &RedBlackTreeMap<K, V>) -> IterArc<'_, K, V> {
        IterArc {
            range_iter: RangeIterArc::new(map, ..),
            size: map.size,
        }
    }
}

impl<'a, K, V> Iterator for IterArc<'a, K, V>
where
    K: Ord,
{
    type Item = &'a Arc<Entry<K, V>>;

    fn next(&mut self) -> Option<&'a Arc<Entry<K, V>>> {
        if self.size > 0 {
            self.size -= 1;
            self.range_iter.next()
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.size, Some(self.size))
    }
}

impl<'a, K, V> DoubleEndedIterator for IterArc<'a, K, V>
where
    K: Ord,
{
    fn next_back(&mut self) -> Option<&'a Arc<Entry<K, V>>> {
        if self.size > 0 {
            self.size -= 1;
            self.range_iter.next_back()
        } else {
            None
        }
    }
}

impl<'a, K: Ord, V> ExactSizeIterator for IterArc<'a, K, V> {}

#[derive(Debug)]
pub struct RangeIterArc<'a, K, V, RB, Q: ?Sized> {
    map: &'a RedBlackTreeMap<K, V>,

    stack_forward: Option<iter_utils::IterStack<'a, K, V>>,
    stack_backward: Option<iter_utils::IterStack<'a, K, V>>,

    range: RB,
    _q: PhantomData<Q>,
}

impl<'a, K, V, Q, RB> RangeIterArc<'a, K, V, RB, Q>
where
    K: Ord + Borrow<Q>,
    Q: Ord + ?Sized,
    RB: RangeBounds<Q>,
{
    fn new(map: &'a RedBlackTreeMap<K, V>, range: RB) -> RangeIterArc<'_, K, V, RB, Q> {
        RangeIterArc {
            map,
            stack_forward: None,
            stack_backward: None,
            range,
            _q: PhantomData,
        }
    }

    fn init_if_needed(&mut self, backwards: bool) {
        use iter_utils::IterStack;

        let stack_field = if backwards {
            &mut self.stack_backward
        } else {
            &mut self.stack_forward
        };

        if stack_field.is_none() {
            *stack_field = Some(IterStack::new(
                self.map,
                self.range.start_bound(),
                self.range.end_bound(),
                backwards,
            ));
        }
    }

    fn is_remaining_range_empty(&self) -> bool {
        match (&self.stack_forward, &self.stack_backward) {
            (Some(stack_forward), Some(stack_backward)) => {
                match (stack_forward.current(), stack_backward.current()) {
                    (Some(left), Some(right)) => left.key > right.key,
                    (_, _) => true,
                }
            }
            (_, _) => false,
        }
    }

    fn current_forward(&self) -> Option<&'a Arc<Entry<K, V>>> {
        match self.is_remaining_range_empty() {
            true => None,
            false => self.stack_forward.as_ref().unwrap().current(),
        }
    }

    fn advance_forward(&mut self) {
        self.stack_forward
            .as_mut()
            .unwrap()
            .advance(self.range.start_bound(), self.range.end_bound());
    }

    fn current_backward(&self) -> Option<&'a Arc<Entry<K, V>>> {
        match self.is_remaining_range_empty() {
            true => None,
            false => self.stack_backward.as_ref().unwrap().current(),
        }
    }

    fn advance_backward(&mut self) {
        self.stack_backward
            .as_mut()
            .unwrap()
            .advance(self.range.start_bound(), self.range.end_bound());
    }
}

impl<'a, K, V, RB, Q> Iterator for RangeIterArc<'a, K, V, RB, Q>
where
    K: Ord + Borrow<Q>,
    Q: Ord + ?Sized,
    RB: RangeBounds<Q>,
{
    type Item = &'a Arc<Entry<K, V>>;

    fn next(&mut self) -> Option<Self::Item> {
        self.init_if_needed(false);

        let current = self.current_forward();

        self.advance_forward();

        current
    }
}

impl<'a, K, V, RB, Q> DoubleEndedIterator for RangeIterArc<'a, K, V, RB, Q>
where
    K: Ord + Borrow<Q>,
    Q: Ord + ?Sized,
    RB: RangeBounds<Q>,
{
    fn next_back(&mut self) -> Option<&'a Arc<Entry<K, V>>> {
        self.init_if_needed(true);

        let current = self.current_backward();

        self.advance_backward();

        current
    }
}

#[cfg(feature = "serde")]
pub mod serde {
    use super::*;
    use ::serde::de::{Deserialize, Deserializer, MapAccess, Visitor};
    use ::serde::ser::{Serialize, Serializer};
    use std::fmt;
    use std::marker::PhantomData;

    impl<K, V> Serialize for RedBlackTreeMap<K, V>
    where
        K: Ord + Serialize,
        V: Serialize,
    {
        fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
            serializer.collect_map(self)
        }
    }

    impl<'de, K, V> Deserialize<'de> for RedBlackTreeMap<K, V>
    where
        K: Ord + Deserialize<'de>,
        V: Deserialize<'de>,
    {
        fn deserialize<D: Deserializer<'de>>(
            deserializer: D,
        ) -> Result<RedBlackTreeMap<K, V>, D::Error> {
            deserializer.deserialize_map(RedBlackTreeMapVisitor {
                phantom: PhantomData,
            })
        }
    }

    struct RedBlackTreeMapVisitor<K, V> {
        phantom: PhantomData<(K, V)>,
    }

    impl<'de, K, V> Visitor<'de> for RedBlackTreeMapVisitor<K, V>
    where
        K: Ord + Deserialize<'de>,
        V: Deserialize<'de>,
    {
        type Value = RedBlackTreeMap<K, V>;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            formatter.write_str("a map")
        }

        fn visit_map<A>(self, mut map: A) -> Result<RedBlackTreeMap<K, V>, A::Error>
        where
            A: MapAccess<'de>,
        {
            let mut rb_tree_map = RedBlackTreeMap::new();

            while let Some((k, v)) = map.next_entry()? {
                rb_tree_map.insert_mut(k, v);
            }

            Ok(rb_tree_map)
        }
    }
}

#[cfg(test)]
mod test;
