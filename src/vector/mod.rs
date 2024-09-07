/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use alloc::borrow::Borrow;
use alloc::fmt::Display;
use alloc::vec;
use alloc::vec::Vec;
use archery::*;
use core::cmp::Ordering;
use core::hash::{Hash, Hasher};
use core::iter::FromIterator;
use core::mem;
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
/// | `insert()`                 | Θ(log(n)) |   Θ(log(n)) |
/// | `remove()`                 | Θ(log(n)) |   Θ(log(n)) |
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
    Branch(Vec<(SharedPointer<Node<T, P>, P>, usize)>),
    Leaf(Vec<SharedPointer<T, P>>),
}

impl<T, P> Node<T, P>
where
    P: SharedPointerKind,
{
    fn new_empty_leaf() -> Node<T, P> {
        Node::Leaf(Vec::new())
    }

    fn get(&self, index: usize) -> &T {
        match self {
            Node::Branch(a) => {
                let mut index = index;
                for &(ref child, len) in a {
                    if index < len {
                        return child.get(index);
                    }
                    index -= len;
                }
                unreachable!()
            }
            Node::Leaf(a) => a[index].as_ref(),
        }
    }

    fn assoc(&mut self, value: T, index: usize) {
        match self {
            Node::Leaf(a) => {
                a[index] = SharedPointer::new(value);
            }
            Node::Branch(a) => {
                let mut index = index;
                for &mut (ref mut child, len) in a.iter_mut() {
                    if index < len {
                        SharedPointer::make_mut(child).assoc(value, index);
                        return;
                    }
                    index -= len;
                }
                unreachable!()
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

    /// Returns the number of elements contained in the node's children.
    fn len(&self) -> usize {
        match self {
            Node::Leaf(a) => a.len(),
            Node::Branch(a) => a.iter().map(|(child, _)| child.len()).sum(),
        }
    }

    /// Inserts a value at the specified index in the node. If the node exceeds the length limit,
    /// it splits the node and returns the additional node.
    ///
    /// # Arguments
    ///
    /// * `index` - The index at which to insert the value.
    /// * `value` - The value to insert.
    /// * `bucket_len_limit` - The maximum length of the node before it needs to be split.
    ///
    /// # Returns
    ///
    /// An `Option` containing the additional node if the node was split, or `None` if no split occurred.
    fn insert(&mut self, index: usize, value: T, bucket_len_limit: usize) -> Option<Node<T, P>> {
        match self {
            Node::Leaf(values) => {
                values.insert(index, SharedPointer::new(value));
                if values.len() > bucket_len_limit {
                    let additional_values = values.split_off(bucket_len_limit / 2);
                    Some(Node::Leaf(additional_values))
                } else {
                    None
                }
            }
            Node::Branch(children) => {
                let mut index = index;
                let split_child = 'insertion: {
                    for (i, (child, len)) in children.iter_mut().enumerate() {
                        if index <= *len {
                            let child = SharedPointer::make_mut(child);
                            let split_child =
                                child.insert(index, value, bucket_len_limit).map(|n| (i, n));
                            *len = child.len();
                            break 'insertion split_child;
                        }
                        index -= *len;
                    }
                    unreachable!()
                };

                let (update_index, additional_child) = split_child?;
                let &mut (ref child, ref mut len) = &mut children[update_index];
                *len = child.len();
                let child_len = additional_child.len();
                children
                    .insert(update_index + 1, (SharedPointer::new(additional_child), child_len));
                if children.len() > bucket_len_limit {
                    let additional_child = children.split_off(bucket_len_limit / 2);
                    Some(Node::Branch(additional_child))
                } else {
                    None
                }
            }
        }
    }

    fn push_back(&mut self, value: T, bucket_len_limit: usize) -> Option<Node<T, P>> {
        match self {
            Node::Leaf(values) => {
                values.push(SharedPointer::new(value));
                if values.len() > bucket_len_limit {
                    let additional_values = values.split_off(bucket_len_limit / 2);
                    Some(Node::Leaf(additional_values))
                } else {
                    None
                }
            }
            Node::Branch(children) => {
                let last = children.last_mut().unwrap();
                let (last_children, last_len) = Self::pair_make_mut(last);
                *last_len += 1;
                let additional_child = last_children.push_back(value, bucket_len_limit);
                if let Some(additional_child) = additional_child {
                    *last_len = last_children.len();
                    let additional_child_len = additional_child.len();
                    children.push((SharedPointer::new(additional_child), additional_child_len));
                    if children.len() > bucket_len_limit {
                        let additional_child = children.split_off(bucket_len_limit / 2);
                        Some(Node::Branch(additional_child))
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
        }
    }

    fn pair_make_mut(
        v: &mut (SharedPointer<Node<T, P>, P>, usize),
    ) -> (&mut Node<T, P>, &mut usize) {
        let (node, len) = v;
        (SharedPointer::make_mut(node), len)
    }

    /// Try to make the center node have at least `bucket_len_limit / 2` children by moving children from the left or right node.
    ///
    /// # Arguments
    ///
    /// * `left` - An optional mutable reference to a tuple containing a mutable reference to the left node and its length.
    /// * `center` - A mutable reference to a tuple containing a mutable reference to the center node and its length.
    /// * `right` - An optional mutable reference to a tuple containing a mutable reference to the right node and its length.
    /// * `bucket_len_limit` - The maximum length of the node before it needs to be split.
    ///
    /// # Returns
    ///
    /// * `true` if the nodes were balanced, `false` otherwise.
    fn balance(
        left: Option<&mut (&mut Node<T, P>, &mut usize)>,
        center: &mut (&mut Node<T, P>, &mut usize),
        right: Option<&mut (&mut Node<T, P>, &mut usize)>,
        bucket_len_limit: usize,
    ) -> bool {
        match (left, center, right) {
            (Some((left_node, left_len)), (center_node, center_len), _)
                if left_node.used() > bucket_len_limit / 2 =>
            {
                fn balance_with_left<T>(
                    left: &mut Vec<T>,
                    center: &mut Vec<T>,
                    bucket_len_limit: usize,
                ) {
                    let split_off_len = (left.len() - bucket_len_limit / 2).div_ceil(2);
                    let mut split_off_vec = left.split_off(left.len() - split_off_len);
                    split_off_vec.append(center);
                    *center = split_off_vec;
                }
                match (&mut *left_node, &mut *center_node) {
                    (Node::Leaf(left), Node::Leaf(center)) => {
                        balance_with_left(left, center, bucket_len_limit);
                    }
                    (Node::Branch(left), Node::Branch(center)) => {
                        balance_with_left(left, center, bucket_len_limit);
                    }
                    _ => unreachable!(),
                }
                **left_len = left_node.len();
                **center_len = center_node.len();
                true
            }
            (_, (center_node, center_len), Some((right_node, right_len)))
                if right_node.used() > bucket_len_limit / 2 =>
            {
                fn balance_with_right<T>(
                    center: &mut Vec<T>,
                    right: &mut Vec<T>,
                    bucket_len_limit: usize,
                ) {
                    let split_off_len = (right.len() - bucket_len_limit / 2).div_ceil(2);
                    let mut split_off_vec = right.split_off(split_off_len);
                    mem::swap(right, &mut split_off_vec);
                    center.extend(split_off_vec);
                }
                match (&mut *center_node, &mut *right_node) {
                    (Node::Leaf(center), Node::Leaf(right)) => {
                        balance_with_right(center, right, bucket_len_limit);
                    }
                    (Node::Branch(center), Node::Branch(right)) => {
                        balance_with_right(center, right, bucket_len_limit);
                    }
                    _ => unreachable!(),
                }
                **center_len = center_node.len();
                **right_len = right_node.len();
                true
            }
            _ => false,
        }
    }

    /// To delete the center node, move the children of the center node to the left or right node.
    ///
    /// # Arguments
    ///
    /// * `left` - An optional mutable reference to a tuple containing a mutable reference to the left node and its length.
    /// * `center` - A mutable reference to a tuple containing a mutable reference to the center node and its length.
    /// * `right` - An optional mutable reference to a tuple containing a mutable reference to the right node and its length.
    /// * `bucket_len_limit` - The maximum length of the node before it needs to be split.
    ///
    /// # Panics
    ///
    /// This function will panic if the nodes cannot be merged within the length limit.
    /// This function is called when balancing by moving elements has failed, so it will not panic.
    fn drain_center(
        left: Option<(&mut Node<T, P>, &mut usize)>,
        center: (&mut Node<T, P>, &mut usize),
        right: Option<(&mut Node<T, P>, &mut usize)>,
        bucket_len_limit: usize,
    ) {
        match (left, center, right) {
            (Some((mut left_node, left_len)), (center_node, _), _)
                if left_node.used() + center_node.used() <= bucket_len_limit =>
            {
                match (&mut left_node, center_node) {
                    (Node::Leaf(left), Node::Leaf(center)) => left.append(center),
                    (Node::Branch(left), Node::Branch(center)) => left.append(center),
                    _ => unreachable!(),
                }
                *left_len = left_node.len();
            }
            (_, (center_node, _), Some((mut right_node, right_len)))
                if center_node.used() + right_node.used() <= bucket_len_limit =>
            {
                match (center_node, &mut right_node) {
                    (Node::Leaf(center), Node::Leaf(right)) => {
                        center.append(right);
                        mem::swap(center, right);
                    }
                    (Node::Branch(center), Node::Branch(right)) => {
                        center.append(right);
                        mem::swap(center, right);
                    }
                    _ => unreachable!(),
                }
                *right_len = right_node.len();
            }
            _ => unreachable!(),
        }
    }

    /// Removes an element at the specified index from the node.
    ///
    /// # Arguments
    ///
    /// * `index` - The index of the element to remove.
    /// * `bucket_len_limit` - The maximum length of the node before it needs to be split.
    ///
    /// # Returns
    ///
    /// `true` if the node requires rebalancing after the removal, `false` otherwise.
    ///
    /// # Panics
    ///
    /// This function will panic if the index is out of bounds.
    fn remove(&mut self, index: usize, bucket_len_limit: usize) -> bool {
        match self {
            Node::Leaf(values) => {
                values.remove(index);
                values.len() < bucket_len_limit / 2
            }
            Node::Branch(children) => {
                let mut index = index;
                let (i, require_removal) = 'removal: {
                    for (i, (child, len)) in children.iter_mut().enumerate() {
                        if index < *len {
                            let require_removal =
                                SharedPointer::make_mut(child).remove(index, bucket_len_limit);
                            *len = child.len();
                            break 'removal (i, require_removal);
                        }
                        index -= *len;
                    }
                    unreachable!()
                };
                if !require_removal {
                    return false;
                }
                let (left, center, right) = match i {
                    0 => {
                        let [center, right] = &mut children[..2] else { unreachable!() };
                        (None, center, Some(right))
                    }
                    i if i < children.len() - 1 => {
                        let [left, center, right] = &mut children[i - 1..=i + 1] else {
                            unreachable!()
                        };
                        (Some(left), center, Some(right))
                    }
                    _ => {
                        let slice_start = children.len() - 2;
                        let [left, center] = &mut children[slice_start..] else { unreachable!() };
                        (Some(left), center, None)
                    }
                };
                let (mut left, mut center, mut right) = (
                    left.map(Self::pair_make_mut),
                    Self::pair_make_mut(center),
                    right.map(Self::pair_make_mut),
                );
                if Self::balance(left.as_mut(), &mut center, right.as_mut(), bucket_len_limit) {
                    return false;
                }
                Self::drain_center(left, center, right, bucket_len_limit);
                children.remove(i);
                children.len() < bucket_len_limit / 2
            }
        }
    }

    /// Drops the last element.
    ///
    /// This will return `true` if the subtree after drop becomes empty (or it already was empty).
    /// Note that this will prune irrelevant branches, i.e. there will be no branches without
    /// elements under it.
    fn drop_last(&mut self, bucket_len_limit: usize) -> bool {
        if self.is_empty() {
            return true;
        }

        match self {
            Node::Leaf(a) => {
                a.pop();
            }

            Node::Branch(a) => {
                let (last_node, last_len) = a.last_mut().unwrap();
                *last_len -= 1;
                if SharedPointer::make_mut(last_node).drop_last(bucket_len_limit) {
                    a.pop();
                }
                if a.len() >= 2 && a.last().unwrap().0.used() < bucket_len_limit / 2 {
                    let range_start = a.len() - 2;
                    let [left, center] = &mut a[range_start..] else { unreachable!() };
                    let mut left = Self::pair_make_mut(left);
                    let mut center = Self::pair_make_mut(center);
                    if !Self::balance(Some(&mut left), &mut center, None, bucket_len_limit) {
                        Self::drain_center(Some(left), center, None, bucket_len_limit);
                        a.pop();
                    }
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
    fn get_mut(&mut self, index: usize) -> &mut T {
        match self {
            Node::Branch(a) => {
                let mut index = index;
                for &mut (ref mut child, len) in a.iter_mut() {
                    if index < len {
                        return SharedPointer::make_mut(child).get_mut(index);
                    }
                    index -= len;
                }
                unreachable!()
            }
            Node::Leaf(a) => SharedPointer::make_mut(&mut a[index]),
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
    fn estimate_height(&self) -> usize {
        if self.length > 1 {
            let u: usize = self.length - 1;
            let c: usize = usize::BITS as usize - u.leading_zeros() as usize;
            let b: usize = self.bits as usize - 1;

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
            Some(self.root.get(index))
        }
    }

    #[must_use]
    pub fn set(&self, index: usize, v: T) -> Option<Vector<T, P>> {
        let mut new_vector = self.clone();

        if new_vector.set_mut(index, v) {
            Some(new_vector)
        } else {
            None
        }
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

    #[must_use]
    pub fn insert(&self, index: usize, v: T) -> Option<Vector<T, P>> {
        let mut new_vector = self.clone();

        if new_vector.insert_mut(index, v) {
            Some(new_vector)
        } else {
            None
        }
    }

    /// Returns `true` if the operation was successful.
    pub fn insert_mut(&mut self, index: usize, v: T) -> bool {
        if index > self.length {
            return false;
        }

        let bucket_len_limit = self.bucket_len_limit();
        self.length += 1;
        let root = SharedPointer::make_mut(&mut self.root);
        let Some(additional_node) = root.insert(index, v, bucket_len_limit) else {
            return true;
        };
        let root_len = root.len();
        let additional_node_len = additional_node.len();
        let new_root = Node::Branch(vec![
            (SharedPointer::clone(&self.root), root_len),
            (SharedPointer::new(additional_node), additional_node_len),
        ]);
        self.root = SharedPointer::new(new_root);

        true
    }

    #[must_use]
    pub fn remove(&self, index: usize) -> Option<Vector<T, P>> {
        let mut new_vector = self.clone();

        if new_vector.remove_mut(index) {
            Some(new_vector)
        } else {
            None
        }
    }

    /// Returns `true` if the operation was successful.
    pub fn remove_mut(&mut self, index: usize) -> bool {
        if index >= self.length {
            return false;
        }

        let bucket_len_limit = self.bucket_len_limit();
        self.length -= 1;
        let root = SharedPointer::make_mut(&mut self.root);
        if root.remove(index, bucket_len_limit) {
            if let Some(new_root) = Vector::compress_root(root) {
                self.root = new_root;
            }
        }

        true
    }

    /// Sets the given index to v.
    ///
    /// # Panics
    ///
    /// This method will panic if the trie's root doesn't have capacity for the given index.
    fn assoc(&mut self, index: usize, v: T) {
        debug_assert!(index < self.len(), "This vector's root cannot support this index");

        SharedPointer::make_mut(&mut self.root).assoc(v, index);
    }

    #[inline]
    fn bucket_len_limit(&self) -> usize {
        vector_utils::degree(self.bits)
    }

    #[must_use]
    pub fn push_back(&self, v: T) -> Vector<T, P> {
        let mut new_vector = self.clone();

        new_vector.push_back_mut(v);

        new_vector
    }

    pub fn push_back_mut(&mut self, v: T) {
        let bucket_len_limit = self.bucket_len_limit();
        self.length += 1;
        let root = SharedPointer::make_mut(&mut self.root);
        let Some(additional_node) = root.push_back(v, bucket_len_limit) else {
            return;
        };
        let root_len = root.len();
        let additional_node_len = additional_node.len();
        let new_root = Node::Branch(vec![
            (SharedPointer::clone(&self.root), root_len),
            (SharedPointer::new(additional_node), additional_node_len),
        ]);
        self.root = SharedPointer::new(new_root);
    }

    /// Compresses a root.  A root is compressed if, whenever there is a branch, it has more than
    /// one child.
    ///
    /// The trie must always have a compressed root.
    fn compress_root(root: &mut Node<T, P>) -> Option<SharedPointer<Node<T, P>, P>> {
        let singleton = root.is_singleton();

        match root {
            Node::Leaf(_) => None,
            Node::Branch(a) if singleton => a.pop().map(|(n, _)| n),
            Node::Branch(_) => None,
        }
    }

    #[must_use]
    pub fn drop_last(&self) -> Option<Vector<T, P>> {
        let mut new_vector = self.clone();

        if new_vector.drop_last_mut() {
            Some(new_vector)
        } else {
            None
        }
    }

    pub fn drop_last_mut(&mut self) -> bool {
        if self.length > 0 {
            let new_root = {
                let bucket_len_limit = self.bucket_len_limit();
                let root = SharedPointer::make_mut(&mut self.root);

                root.drop_last(bucket_len_limit);
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
            Some(SharedPointer::make_mut(&mut self.root).get_mut(index))
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
            Node::Branch(a) => a[self.index as usize].0.as_ref(),
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
                Vec::with_capacity(self.vector.estimate_height() + 1);

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
        if self.non_empty() {
            IterPtr::current(self.stack_forward.as_ref().unwrap())
        } else {
            None
        }
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

impl<'a, T, P> ExactSizeIterator for IterPtr<'a, T, P> where P: SharedPointerKind {}

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
