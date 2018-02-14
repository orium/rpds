/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use std::vec::Vec;
use std::sync::Arc;
use std::borrow::Borrow;
use std::fmt::Display;
use std::cmp::Ordering;
use std::hash::{Hasher, Hash};
use std::ops::Index;
use std::iter::FromIterator;
use std::mem::size_of;

use utils::vec_utils::VecUtils;

// TODO Use impl trait instead of this when available.
pub type Iter<'a, T> = ::std::iter::Map<IterArc<'a, T>, fn(&Arc<T>) -> &T>;

const DEFAULT_BITS: u8 = 5;

/// Creates a [`Vector`](sequence/vector/struct.Vector.html) containing the given arguments:
///
/// ```
/// # use rpds::*;
/// #
/// let v = Vector::new()
///     .push_back(1)
///     .push_back(2)
///     .push_back(3);
///
/// assert_eq!(vector![1, 2, 3], v);
/// ```
#[macro_export]
macro_rules! vector {
    ($($e:expr),*) => {
        {
            #[allow(unused_mut)]
            let mut v = $crate::Vector::new();
            $(
                v = v.push_back($e);
            )*
            v
        }
    };
}

/// A persistent vector with structural sharing.  This data structure supports fast `push_back()`, `set()`,
/// `drop_last()`, and `get()`.
///
/// # Complexity
///
/// Let *n* be the number of elements in the vector.
///
/// ## Temporal complexity
///
/// | Operation                  | Best case | Average   | Worst case  |
/// |:-------------------------- | ---------:| ---------:| -----------:|
/// | `new()`                    |      Θ(1) |      Θ(1) |        Θ(1) |
/// | `set()`                    | Θ(log(n)) | Θ(log(n)) |   Θ(log(n)) |
/// | `push_back()`              | Θ(log(n)) | Θ(log(n)) |   Θ(log(n)) |
/// | `drop_last()`              | Θ(log(n)) | Θ(log(n)) |   Θ(log(n)) |
/// | `first()`/`last()`/`get()` | Θ(log(n)) | Θ(log(n)) |   Θ(log(n)) |
/// | `len()`                    |      Θ(1) |      Θ(1) |        Θ(1) |
/// | `clone()`                  |      Θ(1) |      Θ(1) |        Θ(1) |
/// | iterator creation          |      Θ(1) |      Θ(1) |        Θ(1) |
/// | iterator step              |      Θ(1) |      Θ(1) |   Θ(log(n)) |
/// | iterator full              |      Θ(n) |      Θ(n) |        Θ(n) |
///
/// ### Proof sketch of the complexity of full iteration
///
/// 1. A tree of size *n* and degree *d* has height *⌈log<sub>d</sub>(n)⌉ - 1*.
/// 2. A complete iteration is a depth-first search on the tree.
/// 3. A depth-first search has complexity *Θ(|V| + |E|)*, where *|V|* is the number of nodes and
///    *|E|* the number of edges.
/// 4. The number of nodes *|V|* for a complete tree of height *h* is the sum of powers of *d*, which is
///    *(dʰ - 1) / (d - 1)*. See
///    [Calculating sum of consecutive powers of a number](https://math.stackexchange.com/questions/971761/calculating-sum-of-consecutive-powers-of-a-number).
/// 5. The number of edges is exactly *|V| - 1*.
///
/// By 2. and 3. we have that the complexity of a full iteration is
///
/// ```text
///      Θ(|V| + |E|)
///    = Θ((dʰ - 1) / (d - 1))      (by 4. and 5.)
///    = Θ(dʰ)
///    = Θ(n)                       (by 1.)
/// ```
///
/// # Implementation details
///
/// This vector is implemented as described in
/// [Understanding Persistent Vector Part 1](http://hypirion.com/musings/understanding-persistent-vector-pt-1)
/// and [Understanding Persistent Vector Part 2](http://hypirion.com/musings/understanding-persistent-vector-pt-2).
#[derive(Debug)]
pub struct Vector<T> {
    root: Arc<Node<T>>,
    bits: u8,
    length: usize,
}

#[derive(Debug, PartialEq, Eq)]
enum Node<T> {
    Branch(Vec<Arc<Node<T>>>),
    Leaf(Vec<Arc<T>>),
}

impl<T> Node<T> {
    fn new_empty_branch() -> Node<T> {
        Node::Branch(Vec::new())
    }

    fn new_empty_leaf() -> Node<T> {
        Node::Leaf(Vec::new())
    }

    fn get<F: Fn(usize, usize) -> usize>(&self, index: usize, height: usize, bucket: F) -> &T {
        let b = bucket(index, height);

        match *self {
            Node::Branch(ref a) =>
                a[b].get(index, height - 1, bucket),
            Node::Leaf(ref a) => {
                debug_assert_eq!(height, 0);
                a[b].as_ref()
            },
        }
    }

    fn assoc<F: Fn(usize, usize) -> usize>(
        &self,
        index: usize,
        value: T,
        height: usize,
        bucket: F,
        degree: usize
    ) -> Node<T> {
        let b = bucket(index, height);

        match *self {
            Node::Leaf(ref a) => {
                debug_assert_eq!(height, 0, "cannot have a leaf at this height");

                let new_a = a.cloned_set(b, Arc::new(value));

                Node::Leaf(new_a)
            },

            Node::Branch(ref a) => {
                debug_assert!(height > 0, "cannot have a branch at this height");

                let new_subtree = match a.get(b) {
                    Some(subtree) =>
                        subtree.assoc(index, value, height - 1, bucket, degree),
                    None => {
                        let subtree = if height > 1 {
                            Node::new_empty_branch()
                        } else {
                            Node::new_empty_leaf()
                        };

                        subtree.assoc(index, value, height - 1, bucket, degree)
                    },
                };

                let new_a = a.cloned_set(b, Arc::new(new_subtree));

                Node::Branch(new_a)
            },
        }
    }

    #[inline]
    fn is_empty(&self) -> bool {
        self.used() == 0
    }

    #[inline]
    fn is_singleton(&self) -> bool {
        self.used() == 1
    }

    fn used(&self) -> usize {
        match *self {
            Node::Leaf(ref a)   => a.len(),
            Node::Branch(ref a) => a.len(),
        }
    }

    /// Drops the last element.
    ///
    /// This will return `None` if the subtree after drop becomes empty (or it already was empty).
    /// Note that this will prune irrelevant branches, i.e. there will be no branches without
    /// elements under it.
    fn drop_last(&self) -> Option<Node<T>> {
        if self.is_empty() {
            return None;
        }

        let new_node: Node<T> = match *self {
            Node::Leaf(ref a) => {
                let new_a = a.cloned_remove_last();

                Node::Leaf(new_a)
            },

            Node::Branch(ref a) => {
                let last = a.last().unwrap();

                let new_a = match last.drop_last() {
                    Some(subtree) => a.cloned_set(a.len() - 1, Arc::new(subtree)),
                    None => a.cloned_remove_last(),
                };

                Node::Branch(new_a)
            },
        };

        if new_node.is_empty() { None } else { Some(new_node) }
    }
}

impl<T> Clone for Node<T> {
    fn clone(&self) -> Node<T> {
        match *self {
            Node::Branch(ref a) => Node::Branch(Vec::clone(a)),
            Node::Leaf(ref a)   => Node::Leaf(Vec::clone(a)),
        }
    }
}

impl<T> Vector<T> {
    pub fn new() -> Vector<T> {
        Vector::new_with_bits(DEFAULT_BITS)
    }

    pub fn new_with_bits(bits: u8) -> Vector<T> {
        assert!(bits > 0, "number of bits for the vector must be positive");

        Vector {
            root: Arc::new(Node::new_empty_leaf()),
            bits,
            length: 0
        }
    }

    #[inline]
    pub fn first(&self) -> Option<&T> {
        self.get(0)
    }

    pub fn last(&self) -> Option<&T> {
        match self.length {
            0 => None,
            n => self.get(n - 1),
        }
    }

    #[inline]
    fn degree(&self) -> usize {
        1 << self.bits
    }

    #[inline]
    fn height(&self) -> usize {
        if self.length > 1 {
            let u: usize = self.length - 1;
            let c: usize = 8 * size_of::<usize>() - u.leading_zeros() as usize;
            let b: usize = self.bits as usize;

            c / b + if c % b > 0 { 1 } else { 0 } - 1
        } else {
            0
        }
    }

    #[inline]
    fn mask(&self) -> usize {
        self.degree() - 1
    }

    #[inline]
    fn bucket(&self, index: usize, height: usize) -> usize {
        (index >> (height * self.bits as usize)) & self.mask()
    }

    pub fn get(&self, index: usize) -> Option<&T> {
        if index >= self.length {
            None
        } else {
            Some(self.root.get(index, self.height(), |index, height| self.bucket(index, height)))
        }
    }

    pub fn set(&self, index: usize, v: T) -> Option<Vector<T>> {
        if index >= self.length {
            None
        } else {
            Some(self.assoc(index, v))
        }
    }

    /// Sets the given index to v.
    ///
    /// # Panics
    ///
    /// This method will panic if the trie's root doesn't have capacity for the given index.
    fn assoc(&self, index: usize, v: T) -> Vector<T> {
        debug_assert!(
            index < self.root_max_capacity(),
            "This trie's root cannot support this index"
        );

        let new_root: Node<T> = self.root.assoc(
            index, v, self.height(),
            |index, height| self.bucket(index, height),
            self.degree()
        );
        let adds_item: bool = index >= self.length;

        Vector {
            root: Arc::new(new_root),
            bits: self.bits,
            length: self.length + if adds_item { 1 } else { 0 },
        }
    }

    #[inline]
    fn root_max_capacity(&self) -> usize {
        /* A Trie's root max capacity is
         *
         *     degree ** (height + 1)
         *   = (2 ** bits) ** (height + 1)        (by def. of degree)
         *   = 2 ** (bits * (height + 1))
         *   = 1 << (bits * (height + 1))
         */
        1 << (self.bits as usize * (self.height() + 1))
    }

    #[inline]
    fn is_root_full(&self) -> bool {
        self.length == self.root_max_capacity()
    }

    pub fn push_back(&self, v: T) -> Vector<T> {
        if self.is_root_full() {
            let mut new_root: Node<T> = Node::new_empty_branch();

            match new_root {
                Node::Branch(ref mut values) => values.push(Arc::clone(&self.root)),
                _ => unreachable!("expected a branch")
            }

            let new_vector = Vector {
                root: Arc::new(new_root),
                bits: self.bits,
                length: self.length + 1,
            };

            new_vector.assoc(self.length, v)
        } else  {
            self.assoc(self.length, v)
        }
    }

    /// Compresses a root.  A root is compressed if, whenever there is a branch, it has more than
    /// one child.
    ///
    /// The trie must always have a compressed root.
    fn compress_root(root: Node<T>) -> Node<T> {
        match root {
            leaf@Node::Leaf(_) => leaf,
            branch@Node::Branch(_) =>
                if branch.is_singleton() {
                    if let Node::Branch(a) = branch {
                        Node::clone(a[0].as_ref())
                    } else {
                        unreachable!()
                    }
                } else {
                    branch
                }
        }
    }

    pub fn drop_last(&self) -> Option<Vector<T>> {
        if self.length == 0 {
            return None;
        }

        let new_vector = match self.root.drop_last() {
            None => Vector::new_with_bits(self.bits),
            Some(root) => {
                let new_root: Node<T> = Vector::compress_root(root);

                Vector {
                    root: Arc::new(new_root),
                    bits: self.bits,
                    length: self.length - 1,
                }
            }
        };

        Some(new_vector)
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.length
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn iter(&self) -> Iter<T> {
        self.iter_arc().map(|v| v.borrow())
    }

    fn iter_arc(&self) -> IterArc<T> {
        IterArc::new(self)
    }
}

impl<T> Index<usize> for Vector<T> {
    type Output = T;

    fn index(&self, index: usize) -> &T {
        self.get(index)
            .expect(&format!("index out of bounds {}", index))
    }
}

impl<T> Default for Vector<T> {
    fn default() -> Vector<T> {
        Vector::new()
    }
}

impl<T: PartialEq> PartialEq for Vector<T> {
    fn eq(&self, other: &Vector<T>) -> bool {
        self.length == other.length && self.iter().eq(other.iter())
    }
}

impl<T: Eq> Eq for Vector<T> {}

impl<T: PartialOrd<T>> PartialOrd<Vector<T>> for Vector<T> {
    fn partial_cmp(&self, other: &Vector<T>) -> Option<Ordering> {
        self.iter().partial_cmp(other.iter())
    }
}

impl<T: Ord> Ord for Vector<T> {
    fn cmp(&self, other: &Vector<T>) -> Ordering {
        self.iter().cmp(other.iter())
    }
}

impl<T: Hash> Hash for Vector<T> {
    fn hash<H: Hasher>(&self, state: &mut H) -> () {
        // Add the hash of length so that if two collections are added one after the other it doesn't
        // hash to the same thing as a single collection with the same elements in the same order.
        self.len().hash(state);

        for e in self {
            e.hash(state);
        }
    }
}

impl<T> Clone for Vector<T> {
    fn clone(&self) -> Vector<T> {
        Vector {
            root: Arc::clone(&self.root),
            bits: self.bits,
            length: self.length,
        }
    }
}

impl<T> Display for Vector<T>
    where T: Display {
    fn fmt(&self, fmt: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        let mut first = true;

        fmt.write_str("[")?;

        for v in self.iter() {
            if !first {
                fmt.write_str(", ")?;
            }
            v.fmt(fmt)?;
            first = false;
        }

        fmt.write_str("]")
    }
}

impl<'a, T> IntoIterator for &'a Vector<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Iter<'a, T> {
        self.iter()
    }
}

impl<T> FromIterator<T> for Vector<T> {
    fn from_iter<I: IntoIterator<Item = T>>(into_iter: I) -> Vector<T> {
        let mut vector = Vector::new();

        for e in into_iter {
            vector = vector.push_back(e);
        }

        vector
    }
}

pub struct IterArc<'a, T: 'a> {
    vector: &'a Vector<T>,

    stack_forward:  Option<Vec<IterStackElement<'a, T>>>,
    stack_backward: Option<Vec<IterStackElement<'a, T>>>,

    left_index:  usize, // inclusive
    right_index: usize, // exclusive
}

struct IterStackElement<'a, T: 'a> {
    node: &'a Node<T>,
    index: isize,
}

impl<'a, T> IterStackElement<'a, T> {
    fn new(node: &Node<T>, backwards: bool) -> IterStackElement<T> {
        IterStackElement {
            node,
            index: if backwards { node.used() as isize - 1 } else { 0 },
        }
    }

    fn current_node(&self) -> &'a Node<T> {
        match *self.node {
            Node::Branch(ref a) => a[self.index as usize].as_ref(),
            Node::Leaf(_) => panic!("called current node of a branch"),
        }
    }

    fn current_elem(&self) -> &'a Arc<T> {
        match *self.node {
            Node::Leaf(ref a) => &a[self.index as usize],
            Node::Branch(_) => panic!("called current element of a branch"),
        }
    }

    /// Advance and returns `true` if finished.
    #[inline]
    fn advance(&mut self, backwards: bool) -> bool {
        if backwards {
            self.index -= 1;
            self.index < 0
        } else {
            self.index += 1;
            self.index as usize >= self.node.used()
        }
    }
}

impl<'a, T> IterArc<'a, T> {
    fn new(vector: &Vector<T>) -> IterArc<T> {
        IterArc {
            vector,

            stack_forward:  None,
            stack_backward: None,

            left_index: 0,
            right_index: vector.len(),
        }
    }

    fn dig(stack: &mut Vec<IterStackElement<T>>, backwards: bool) -> () {
        let next_node: &Node<T> = {
            let stack_top = stack.last().unwrap();

            if let Node::Leaf(_) = *stack_top.node {
                return;
            }

            stack_top.current_node()
        };

        stack.push(IterStackElement::new(next_node, backwards));

        IterArc::dig(stack, backwards);
    }

    fn init_if_needed(&mut self, backwards: bool) -> () {
        let stack_field = if backwards {
            &mut self.stack_backward
        } else {
            &mut self.stack_forward
        };

        if stack_field.is_none() {
            let mut stack: Vec<IterStackElement<T>> = Vec::with_capacity(self.vector.height() + 1);

            stack.push(IterStackElement::new(self.vector.root.borrow(), backwards));

            IterArc::dig(&mut stack, backwards);

            *stack_field = Some(stack);
        }
    }

    fn advance(stack: &mut Vec<IterStackElement<T>>, backwards: bool) -> () {
        match stack.pop() {
            Some(mut stack_element) => {
                let finished = stack_element.advance(backwards);

                if finished {
                    IterArc::advance(stack, backwards);
                } else {
                    stack.push(stack_element);

                    IterArc::dig(stack, backwards);
                }
            },
            None => (), // Reached the end.  Nothing to do.
        }
    }

    #[inline]
    fn current(stack: &[IterStackElement<'a, T>]) -> Option<&'a Arc<T>> {
        stack.last().map(|e| e.current_elem())
    }

    #[inline]
    fn non_empty(&self) -> bool {
        self.left_index < self.right_index
    }

    fn advance_forward(&mut self) -> () {
        if self.non_empty() {
            IterArc::advance(self.stack_forward.as_mut().unwrap(), false);

            self.left_index += 1;
        }
    }

    fn current_forward(&self) -> Option<&'a Arc<T>> {
        if self.non_empty() {
            IterArc::current(self.stack_forward.as_ref().unwrap())
        } else {
            None
        }
    }

    fn advance_backward(&mut self) -> () {
        if self.non_empty() {
            IterArc::advance(self.stack_backward.as_mut().unwrap(), true);

            self.right_index -= 1;
        }
    }

    fn current_backward(&self) -> Option<&'a Arc<T>> {
        if self.non_empty() {
            IterArc::current(self.stack_backward.as_ref().unwrap())
        } else {
            None
        }
    }
}

impl<'a, T> Iterator for IterArc<'a, T> {
    type Item = &'a Arc<T>;

    fn next(&mut self) -> Option<&'a Arc<T>> {
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

impl<'a, T> DoubleEndedIterator for IterArc<'a, T> {
    fn next_back(&mut self) -> Option<&'a Arc<T>> {
        self.init_if_needed(true);

        let current = self.current_backward();

        self.advance_backward();

        current
    }
}

impl<'a, T> ExactSizeIterator for IterArc<'a, T> {}

#[cfg(feature = "serde")]
pub mod serde {
    use super::*;
    use serde::ser::{Serialize, Serializer};
    use serde::de::{Deserialize, Deserializer, SeqAccess, Visitor};
    use std::marker::PhantomData;
    use std::fmt;

    impl<T> Serialize for Vector<T>
        where T: Serialize {
        fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
            serializer.collect_seq(self)
        }
    }

    impl<'de, T> Deserialize<'de> for Vector<T>
        where T: Deserialize<'de> {
        fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Vector<T>, D::Error> {
            deserializer.deserialize_seq(VectorVisitor { phantom: PhantomData } )
        }
    }

    struct VectorVisitor<T> {
        phantom: PhantomData<T>
    }

    impl<'de, T> Visitor<'de> for VectorVisitor<T>
        where T: Deserialize<'de> {
        type Value = Vector<T>;

        fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
            formatter.write_str("a sequence")
        }

        fn visit_seq<A>(self, mut seq: A) -> Result<Vector<T>, A::Error>
            where A: SeqAccess<'de> {
            let mut vector = Vector::new();

            while let Some(value) = seq.next_element()? {
                vector = vector.push_back(value);
            }

            Ok(vector)
        }
    }
}

#[cfg(test)]
mod test;
