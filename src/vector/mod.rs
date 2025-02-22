/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use alloc::borrow::Borrow;
use alloc::fmt::Display;
use alloc::vec::Vec;
use archery::*;
use core::cmp::Ordering;
use core::hash::{Hash, Hasher};
use core::iter::FromIterator;
use core::ops::Index;
use core::ops::IndexMut;

// TODO Use impl trait instead of this when available.
pub type Iter<'a, T, P> = core::iter::Map<IterPtr<'a, T, P>, fn(&SharedPointer<T, P>) -> &T>;

const DEFAULT_BITS: u8 = 5;

/// Creates a [`Vector`](crate::Vector) containing the given arguments:
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
                v.push_back_mut($e);
            )*
            v
        }
    };
}

/// Creates a [`Vector`](crate::Vector) that implements `Sync`, containing the given arguments:
///
/// ```
/// # use rpds::*;
/// #
/// let v = Vector::new_sync()
///     .push_back(1)
///     .push_back(2)
///     .push_back(3);
///
/// assert_eq!(vector_sync![1, 2, 3], v);
/// ```
#[macro_export]
macro_rules! vector_sync {
    ($($e:expr),*) => {
        {
            #[allow(unused_mut)]
            let mut v = $crate::Vector::new_sync();
            $(
                v.push_back_mut($e);
            )*
            v
        }
    };
}

/// A persistent vector with structural sharing.
///
/// # Complexity
///
/// Let *n* be the number of elements in the vector.
///
/// ## Temporal complexity
///
/// | Operation                  | Average   | Worst case  |
/// |:-------------------------- | ---------:| -----------:|
/// | `new()`                    |      Θ(1) |        Θ(1) |
/// | `set()`                    | Θ(log(n)) |   Θ(log(n)) |
/// | `push_back()`              | Θ(log(n)) |   Θ(log(n)) |
/// | `drop_last()`              | Θ(log(n)) |   Θ(log(n)) |
/// | `first()`/`last()`/`get()` | Θ(log(n)) |   Θ(log(n)) |
/// | `len()`                    |      Θ(1) |        Θ(1) |
/// | `clone()`                  |      Θ(1) |        Θ(1) |
/// | iterator creation          |      Θ(1) |        Θ(1) |
/// | iterator step              |      Θ(1) |   Θ(log(n)) |
/// | iterator full              |      Θ(n) |        Θ(n) |
///
/// # Implementation details
///
/// This implementation uses a bitmapped vector trie as described in
/// [Understanding Persistent Vector Part 1](http://hypirion.com/musings/understanding-persistent-vector-pt-1)
/// and [Understanding Persistent Vector Part 2](http://hypirion.com/musings/understanding-persistent-vector-pt-2).
#[derive(Debug)]
pub struct Vector<T, P = RcK>
where
    P: SharedPointerKind,
{
    root: SharedPointer<Node<T, P>, P>,
    bits: u8,
    length: usize,
}

pub type VectorSync<T> = Vector<T, ArcTK>;

#[derive(Debug)]
enum Node<T, P = RcK>
where
    P: SharedPointerKind,
{
    Branch(Vec<SharedPointer<Node<T, P>, P>>),
    Leaf(Vec<SharedPointer<T, P>>),
}

impl<T, P> Node<T, P>
where
    P: SharedPointerKind,
{
    fn new_empty_branch() -> Node<T, P> {
        Node::Branch(Vec::new())
    }

    fn new_empty_leaf() -> Node<T, P> {
        Node::Leaf(Vec::new())
    }

    fn get<F: Fn(usize, usize) -> usize>(&self, index: usize, height: usize, bucket: F) -> &T {
        let b = bucket(index, height);

        match self {
            Node::Branch(a) => a[b].get(index, height - 1, bucket),
            Node::Leaf(a) => {
                debug_assert_eq!(height, 0);
                a[b].as_ref()
            }
        }
    }

    fn assoc<F: Fn(usize) -> usize>(&mut self, value: T, height: usize, bucket: F) {
        let b = bucket(height);

        match self {
            Node::Leaf(a) => {
                debug_assert_eq!(height, 0, "cannot have a leaf at this height");

                if a.len() == b {
                    a.push(SharedPointer::new(value));
                } else {
                    a[b] = SharedPointer::new(value);
                }
            }

            Node::Branch(a) => {
                debug_assert!(height > 0, "cannot have a branch at this height");

                match a.get_mut(b) {
                    Some(subtree) => {
                        SharedPointer::make_mut(subtree).assoc(value, height - 1, bucket);
                    }
                    None => {
                        let mut subtree = if height > 1 {
                            Node::new_empty_branch()
                        } else {
                            Node::new_empty_leaf()
                        };

                        subtree.assoc(value, height - 1, bucket);
                        a.push(SharedPointer::new(subtree));
                    }
                }
            }
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
        match self {
            Node::Leaf(a) => a.len(),
            Node::Branch(a) => a.len(),
        }
    }

    /// Drops the last element.
    ///
    /// This will return `true` if the subtree after drop becomes empty (or it already was empty).
    /// Note that this will prune irrelevant branches, i.e. there will be no branches without
    /// elements under it.
    fn drop_last(&mut self) -> bool {
        if self.is_empty() {
            return true;
        }

        match self {
            Node::Leaf(a) => {
                a.pop();
            }

            Node::Branch(a) => {
                if SharedPointer::make_mut(a.last_mut().unwrap()).drop_last() {
                    a.pop();
                }
            }
        }

        self.is_empty()
    }
}

impl<T: Clone, P> Node<T, P>
where
    P: SharedPointerKind,
{
    fn get_mut<F: Fn(usize, usize) -> usize>(
        &mut self,
        index: usize,
        height: usize,
        bucket: F,
    ) -> &mut T {
        let b = bucket(index, height);

        match *self {
            Node::Branch(ref mut a) => {
                SharedPointer::make_mut(&mut a[b]).get_mut(index, height - 1, bucket)
            }
            Node::Leaf(ref mut a) => {
                debug_assert_eq!(height, 0);
                SharedPointer::make_mut(&mut a[b])
            }
        }
    }
}

impl<T, P> Clone for Node<T, P>
where
    P: SharedPointerKind,
{
    fn clone(&self) -> Node<T, P> {
        match self {
            Node::Branch(a) => Node::Branch(Vec::clone(a)),
            Node::Leaf(a) => Node::Leaf(Vec::clone(a)),
        }
    }
}

mod vector_utils {
    #[inline]
    pub fn degree(bits: u8) -> usize {
        1 << bits
    }

    #[inline]
    pub fn mask(bits: u8) -> usize {
        degree(bits) - 1
    }

    #[inline]
    pub fn bucket(bits: u8, index: usize, height: usize) -> usize {
        (index >> (height * bits as usize)) & mask(bits)
    }
}

impl<T> VectorSync<T> {
    #[must_use]
    pub fn new_sync() -> VectorSync<T> {
        Vector::new_with_ptr_kind()
    }
}

impl<T> Vector<T> {
    #[must_use]
    pub fn new() -> Vector<T> {
        Vector::new_with_ptr_kind()
    }
}

impl<T, P> Vector<T, P>
where
    P: SharedPointerKind,
{
    #[must_use]
    pub fn new_with_ptr_kind() -> Vector<T, P> {
        Vector::new_with_bits(DEFAULT_BITS)
    }

    #[must_use]
    pub fn new_with_bits(bits: u8) -> Vector<T, P> {
        assert!(bits > 0, "number of bits for the vector must be positive");

        Vector { root: SharedPointer::new(Node::new_empty_leaf()), bits, length: 0 }
    }

    #[must_use]
    #[inline]
    pub fn first(&self) -> Option<&T> {
        self.get(0)
    }

    #[must_use]
    pub fn last(&self) -> Option<&T> {
        match self.length {
            0 => None,
            n => self.get(n - 1),
        }
    }

    #[inline]
    fn height(&self) -> usize {
        if self.length > 1 {
            let u: usize = self.length - 1;
            let c: usize = usize::BITS as usize - u.leading_zeros() as usize;
            let b: usize = self.bits as usize;

            c / b + usize::from(c % b > 0) - 1
        } else {
            0
        }
    }

    #[must_use]
    pub fn get(&self, index: usize) -> Option<&T> {
        if index >= self.length {
            None
        } else {
            Some(self.root.get(index, self.height(), |index, height| {
                vector_utils::bucket(self.bits, index, height)
            }))
        }
    }

    #[must_use]
    pub fn set(&self, index: usize, v: T) -> Option<Vector<T, P>> {
        let mut new_vector = self.clone();

        if new_vector.set_mut(index, v) { Some(new_vector) } else { None }
    }

    /// Returns `true` if the operation was successful.
    pub fn set_mut(&mut self, index: usize, v: T) -> bool {
        if index >= self.length {
            false
        } else {
            self.assoc(index, v);
            true
        }
    }

    /// Sets the given index to v.
    ///
    /// # Panics
    ///
    /// This method will panic if the trie's root doesn't have capacity for the given index.
    fn assoc(&mut self, index: usize, v: T) {
        debug_assert!(
            index < self.root_max_capacity(),
            "This trie's root cannot support this index"
        );

        let height = self.height();
        let bits = self.bits;
        SharedPointer::make_mut(&mut self.root)
            .assoc(v, height, |height| vector_utils::bucket(bits, index, height));
        let adds_item: bool = index >= self.length;

        if adds_item {
            self.length += 1;
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

    #[must_use]
    pub fn push_back(&self, v: T) -> Vector<T, P> {
        let mut new_vector = self.clone();

        new_vector.push_back_mut(v);

        new_vector
    }

    pub fn push_back_mut(&mut self, v: T) {
        if self.is_root_full() {
            let mut new_root: Node<T, P> = Node::new_empty_branch();

            match new_root {
                Node::Branch(ref mut values) => values.push(SharedPointer::clone(&self.root)),
                Node::Leaf(_) => unreachable!("expected a branch"),
            }

            let length = self.length;
            self.root = SharedPointer::new(new_root);
            self.length += 1;

            self.assoc(length, v);
        } else {
            let length = self.length;
            self.assoc(length, v);
        }
    }

    /// Compresses a root.  A root is compressed if, whenever there is a branch, it has more than
    /// one child.
    ///
    /// The trie must always have a compressed root.
    fn compress_root(root: &mut Node<T, P>) -> Option<SharedPointer<Node<T, P>, P>> {
        let singleton = root.is_singleton();

        match root {
            Node::Leaf(_) => None,
            Node::Branch(a) if singleton => a.pop(),
            Node::Branch(_) => None,
        }
    }

    #[must_use]
    pub fn drop_last(&self) -> Option<Vector<T, P>> {
        let mut new_vector = self.clone();

        if new_vector.drop_last_mut() { Some(new_vector) } else { None }
    }

    pub fn drop_last_mut(&mut self) -> bool {
        if self.length > 0 {
            let new_root = {
                let root = SharedPointer::make_mut(&mut self.root);

                root.drop_last();
                self.length -= 1;

                Vector::compress_root(root)
            };

            if let Some(new_root) = new_root {
                self.root = new_root;
            }

            true
        } else {
            false
        }
    }

    #[must_use]
    #[inline]
    pub fn len(&self) -> usize {
        self.length
    }

    #[must_use]
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn iter(&self) -> Iter<'_, T, P> {
        self.iter_ptr().map(|v| v.borrow())
    }

    #[must_use]
    fn iter_ptr(&self) -> IterPtr<'_, T, P> {
        IterPtr::new(self)
    }
}

impl<T: Clone, P> Vector<T, P>
where
    P: SharedPointerKind,
{
    /// Gets a mutable reference to an element. If the element is shared, it will be cloned.
    /// Returns `None` if and only if the given `index` is out of range.
    #[must_use]
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        if index >= self.length {
            None
        } else {
            let height = self.height();
            let bits = self.bits;
            Some(
                SharedPointer::make_mut(&mut self.root).get_mut(index, height, |index, height| {
                    vector_utils::bucket(bits, index, height)
                }),
            )
        }
    }
}

impl<T, P> Index<usize> for Vector<T, P>
where
    P: SharedPointerKind,
{
    type Output = T;

    fn index(&self, index: usize) -> &T {
        self.get(index).unwrap_or_else(|| panic!("index out of bounds {index}"))
    }
}

impl<T: Clone, P> IndexMut<usize> for Vector<T, P>
where
    P: SharedPointerKind,
{
    fn index_mut(&mut self, index: usize) -> &mut T {
        self.get_mut(index).unwrap_or_else(|| panic!("index out of bounds {index}"))
    }
}

impl<T, P> Default for Vector<T, P>
where
    P: SharedPointerKind,
{
    fn default() -> Vector<T, P> {
        Vector::new_with_ptr_kind()
    }
}

impl<T: PartialEq<U>, U, P, PO> PartialEq<Vector<U, PO>> for Vector<T, P>
where
    P: SharedPointerKind,
    PO: SharedPointerKind,
{
    fn eq(&self, other: &Vector<U, PO>) -> bool {
        self.length == other.length && self.iter().eq(other.iter())
    }
}

impl<T: Eq, P> Eq for Vector<T, P> where P: SharedPointerKind {}

impl<T: PartialOrd<U>, U, P, PO> PartialOrd<Vector<U, PO>> for Vector<T, P>
where
    P: SharedPointerKind,
    PO: SharedPointerKind,
{
    fn partial_cmp(&self, other: &Vector<U, PO>) -> Option<Ordering> {
        self.iter().partial_cmp(other.iter())
    }
}

impl<T: Ord, P> Ord for Vector<T, P>
where
    P: SharedPointerKind,
{
    fn cmp(&self, other: &Vector<T, P>) -> Ordering {
        self.iter().cmp(other.iter())
    }
}

impl<T: Hash, P> Hash for Vector<T, P>
where
    P: SharedPointerKind,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Add the hash of length so that if two collections are added one after the other it doesn't
        // hash to the same thing as a single collection with the same elements in the same order.
        self.len().hash(state);

        for e in self {
            e.hash(state);
        }
    }
}

impl<T, P> Clone for Vector<T, P>
where
    P: SharedPointerKind,
{
    fn clone(&self) -> Vector<T, P> {
        Vector { root: SharedPointer::clone(&self.root), bits: self.bits, length: self.length }
    }
}

impl<T: Display, P> Display for Vector<T, P>
where
    P: SharedPointerKind,
{
    fn fmt(&self, fmt: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let mut first = true;

        fmt.write_str("[")?;

        for v in self {
            if !first {
                fmt.write_str(", ")?;
            }
            v.fmt(fmt)?;
            first = false;
        }

        fmt.write_str("]")
    }
}

impl<'a, T, P> IntoIterator for &'a Vector<T, P>
where
    P: SharedPointerKind,
{
    type Item = &'a T;
    type IntoIter = Iter<'a, T, P>;

    fn into_iter(self) -> Iter<'a, T, P> {
        self.iter()
    }
}

impl<T, P> FromIterator<T> for Vector<T, P>
where
    P: SharedPointerKind,
{
    fn from_iter<I: IntoIterator<Item = T>>(into_iter: I) -> Vector<T, P> {
        let mut vector = Vector::new_with_ptr_kind();
        vector.extend(into_iter);
        vector
    }
}

impl<T, P> Extend<T> for Vector<T, P>
where
    P: SharedPointerKind,
{
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for elem in iter {
            self.push_back_mut(elem);
        }
    }
}

pub struct IterPtr<'a, T, P>
where
    P: SharedPointerKind,
{
    vector: &'a Vector<T, P>,

    stack_forward: Option<Vec<IterStackElement<'a, T, P>>>,
    stack_backward: Option<Vec<IterStackElement<'a, T, P>>>,

    left_index: usize,  // inclusive
    right_index: usize, // exclusive
}

struct IterStackElement<'a, T, P>
where
    P: SharedPointerKind,
{
    node: &'a Node<T, P>,
    index: isize,
}

impl<'a, T, P> IterStackElement<'a, T, P>
where
    P: SharedPointerKind,
{
    fn new(node: &Node<T, P>, backwards: bool) -> IterStackElement<'_, T, P> {
        #[allow(clippy::cast_possible_wrap)]
        IterStackElement { node, index: if backwards { node.used() as isize - 1 } else { 0 } }
    }

    #[inline]
    fn current_node(&self) -> &'a Node<T, P> {
        #[allow(clippy::cast_sign_loss)]
        match self.node {
            Node::Branch(a) => a[self.index as usize].as_ref(),
            Node::Leaf(_) => panic!("called current node of a branch"),
        }
    }

    #[inline]
    fn current_elem(&self) -> &'a SharedPointer<T, P> {
        #[allow(clippy::cast_sign_loss)]
        match self.node {
            Node::Leaf(a) => &a[self.index as usize],
            Node::Branch(_) => panic!("called current element of a branch"),
        }
    }

    /// Advance and returns `true` if finished.
    #[inline]
    fn advance(&mut self, backwards: bool) -> bool {
        #[allow(clippy::cast_sign_loss)]
        if backwards {
            self.index -= 1;
            self.index < 0
        } else {
            self.index += 1;
            self.index as usize >= self.node.used()
        }
    }
}

impl<'a, T, P> IterPtr<'a, T, P>
where
    P: SharedPointerKind,
{
    fn new(vector: &Vector<T, P>) -> IterPtr<'_, T, P> {
        IterPtr {
            vector,

            stack_forward: None,
            stack_backward: None,

            left_index: 0,
            right_index: vector.len(),
        }
    }

    fn dig(stack: &mut Vec<IterStackElement<'_, T, P>>, backwards: bool) {
        let next_node: &Node<T, P> = {
            let stack_top = stack.last().unwrap();

            if let Node::Leaf(_) = *stack_top.node {
                return;
            }

            stack_top.current_node()
        };

        stack.push(IterStackElement::new(next_node, backwards));

        IterPtr::dig(stack, backwards);
    }

    fn init_if_needed(&mut self, backwards: bool) {
        let stack_field =
            if backwards { &mut self.stack_backward } else { &mut self.stack_forward };

        if stack_field.is_none() {
            let mut stack: Vec<IterStackElement<'_, T, P>> =
                Vec::with_capacity(self.vector.height() + 1);

            stack.push(IterStackElement::new(self.vector.root.borrow(), backwards));

            IterPtr::dig(&mut stack, backwards);

            *stack_field = Some(stack);
        }
    }

    fn advance(stack: &mut Vec<IterStackElement<'_, T, P>>, backwards: bool) {
        if let Some(mut stack_element) = stack.pop() {
            let finished = stack_element.advance(backwards);

            if finished {
                IterPtr::advance(stack, backwards);
            } else {
                stack.push(stack_element);

                IterPtr::dig(stack, backwards);
            }
        }
    }

    #[inline]
    fn current(stack: &[IterStackElement<'a, T, P>]) -> Option<&'a SharedPointer<T, P>> {
        stack.last().map(IterStackElement::current_elem)
    }

    #[inline]
    fn non_empty(&self) -> bool {
        self.left_index < self.right_index
    }

    fn advance_forward(&mut self) {
        if self.non_empty() {
            IterPtr::advance(self.stack_forward.as_mut().unwrap(), false);

            self.left_index += 1;
        }
    }

    fn current_forward(&self) -> Option<&'a SharedPointer<T, P>> {
        if self.non_empty() { IterPtr::current(self.stack_forward.as_ref().unwrap()) } else { None }
    }

    fn advance_backward(&mut self) {
        if self.non_empty() {
            IterPtr::advance(self.stack_backward.as_mut().unwrap(), true);

            self.right_index -= 1;
        }
    }

    fn current_backward(&self) -> Option<&'a SharedPointer<T, P>> {
        if self.non_empty() {
            IterPtr::current(self.stack_backward.as_ref().unwrap())
        } else {
            None
        }
    }
}

impl<'a, T, P> Iterator for IterPtr<'a, T, P>
where
    P: SharedPointerKind,
{
    type Item = &'a SharedPointer<T, P>;

    fn next(&mut self) -> Option<&'a SharedPointer<T, P>> {
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

impl<'a, T, P> DoubleEndedIterator for IterPtr<'a, T, P>
where
    P: SharedPointerKind,
{
    fn next_back(&mut self) -> Option<&'a SharedPointer<T, P>> {
        self.init_if_needed(true);

        let current = self.current_backward();

        self.advance_backward();

        current
    }
}

impl<T, P> ExactSizeIterator for IterPtr<'_, T, P> where P: SharedPointerKind {}

#[cfg(feature = "serde")]
pub mod serde {
    use super::*;
    use ::serde::de::{Deserialize, Deserializer, SeqAccess, Visitor};
    use ::serde::ser::{Serialize, Serializer};
    use core::fmt;
    use core::marker::PhantomData;

    impl<T, P> Serialize for Vector<T, P>
    where
        T: Serialize,
        P: SharedPointerKind,
    {
        fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
            serializer.collect_seq(self)
        }
    }

    impl<'de, T, P> Deserialize<'de> for Vector<T, P>
    where
        T: Deserialize<'de>,
        P: SharedPointerKind,
    {
        fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Vector<T, P>, D::Error> {
            deserializer
                .deserialize_seq(VectorVisitor { _phantom_t: PhantomData, _phantom_p: PhantomData })
        }
    }

    struct VectorVisitor<T, P> {
        _phantom_t: PhantomData<T>,
        _phantom_p: PhantomData<P>,
    }

    impl<'de, T, P> Visitor<'de> for VectorVisitor<T, P>
    where
        T: Deserialize<'de>,
        P: SharedPointerKind,
    {
        type Value = Vector<T, P>;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            formatter.write_str("a sequence")
        }

        fn visit_seq<A>(self, mut seq: A) -> Result<Vector<T, P>, A::Error>
        where
            A: SeqAccess<'de>,
        {
            let mut vector = Vector::new_with_ptr_kind();

            while let Some(value) = seq.next_element()? {
                vector.push_back_mut(value);
            }

            Ok(vector)
        }
    }
}

#[cfg(test)]
mod test;
