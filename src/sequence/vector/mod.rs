/* This file is part of rpds.
 *
 * rpds is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * rpds is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with rpds.  If not, see <http://www.gnu.org/licenses/>.
 */

use std::vec::Vec;
use std::sync::Arc;
use std::fmt::Display;
use std::cmp::Ordering;
use std::hash::{Hasher, Hash};
use std::ops::Index;
use std::iter::FromIterator;
use std::mem::size_of;

const DEFAULT_BITS: u8 = 5;

trait CloneWithCapacity {
    fn clone_with_capacity(&self, capacity: usize) -> Self;
}

impl<T: Clone> CloneWithCapacity for Vec<T> {
    fn clone_with_capacity(&self, capacity: usize) -> Self {
        let mut vec: Vec<T> = Vec::with_capacity(capacity.max(self.len()));

        vec.extend_from_slice(self);

        vec
    }
}

/// A persistent vector with structural sharing.  This data structure supports fast get, set,
/// and push.
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
/// | `first()`/`last()`/`get()` | Θ(log(n)) | Θ(log(n)) |   Θ(log(n)) |
/// | `set()`                    | Θ(log(n)) | Θ(log(n)) |   Θ(log(n)) |
/// | `push()`                   | Θ(log(n)) | Θ(log(n)) |   Θ(log(n)) |
/// | `drop_last()`              | Θ(log(n)) | Θ(log(n)) |   Θ(log(n)) |
/// | `clone()`                  |      Θ(1) |      Θ(1) |        Θ(1) |
/// | `len()`                    |      Θ(1) |      Θ(1) |        Θ(1) |
/// | iterator creation          |      Θ(1) |      Θ(1) |        Θ(1) |
/// | iterator step              |      Θ(1) |      Θ(1) |   Θ(log(n)) |
/// | iterator full              |      Θ(n) |      Θ(n) |        Θ(n) |
///
/// ### Proof sketch of the complexity of full iteration
///
/// 1. A tree of size *n* and degree *d* has height *⌈log_d(n)⌉ - 1*.
/// 2. A complete iteration is a depth-first search on the tree.
/// 3. A depth-first search has complexity *Θ(|V| + |E|)*, where *|V|* is the number of nodes and
///    *|E|* the number of edges.
/// 4. The number of nodes *|V|* for a complete tree of height *h* is the sum of powers of *d*, which is
///    *(d ** h - 1) / (d - 1)*. See
///    [Calculating sum of consecutive powers of a number](https://math.stackexchange.com/questions/971761/calculating-sum-of-consecutive-powers-of-a-number)).
/// 5. The number of edges is exactly *|V| - 1*.
///
/// By 2. and 3. we have that the complexity of a full iteration is
///
/// ```text
///      Θ(|V| + |E|)
///    = Θ((d ** h - 1) / (d - 1))      (by 4. and 5.)
///    = Θ(d ** h)
///    = Θ(n)                           (by 1.)
/// ```
///
/// ## Space complexity
///
/// The space complexity is *Θ(n)*.
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
        fn set_array<V>(array: &mut Vec<V>, index: usize, value: V) -> () {
            if index < array.len() {
                array[index] = value;
            } else if index == array.len() {
                array.push(value);
            } else {
                unreachable!();
            }
        }

        let b = bucket(index, height);

        match *self {
            Node::Leaf(ref a) => {
                debug_assert_eq!(height, 0, "Cannot have a leaf at this height");

                let mut a = Vec::clone_with_capacity(a, b + 1);

                set_array(&mut a, b, Arc::new(value));

                Node::Leaf(a)
            },

            Node::Branch(ref a) => {
                debug_assert!(height > 0, "Cannot have a branch at this height");

                let mut a = Vec::clone_with_capacity(a, b + 1);

                let subtree: Node<T> = match a.get(b) {
                    Some(s) => Node::clone(s),
                    None =>
                        if height > 1 {
                            Node::new_empty_branch()
                        } else {
                            Node::new_empty_leaf()
                        },
                };

                set_array(&mut a, b, Arc::new(subtree.assoc(index, value, height - 1, bucket, degree)));

                Node::Branch(a)
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
                let new_a = a[0..(a.len() - 1)].to_vec();

                Node::Leaf(new_a)
            },

            Node::Branch(ref a) => {
                let mut new_a = Vec::clone(a);
                let new_child: Option<Node<T>> =
                    new_a.pop().unwrap().drop_last();

                if let Some(child_node) = new_child {
                    new_a.push(Arc::new(child_node));
                }

                Node::Branch(new_a)
            },
        };

        if new_node.is_empty() { None } else { Some(new_node) }
    }
}

impl<T> Clone for Node<T> {
    fn clone(&self) -> Node<T> {
        match *self {
            Node::Branch(ref a) => Node::Branch(Vec::clone(&a)),
            Node::Leaf(ref a)   => Node::Leaf(Vec::clone(&a)),
        }
    }
}

impl<T> Vector<T> {
    pub fn new() -> Vector<T> {
        Vector::new_with_bits(DEFAULT_BITS)
    }

    pub fn new_with_bits(bits: u8) -> Vector<T> {
        assert!(bits > 0, "Number of bits for the vector must be positive");

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

    /// Sets the given index to v.  This method does not guarantee that that vector is continuous.
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

    pub fn push(&self, v: T) -> Vector<T> {
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

    /// Compresses a root.  A root is compressed if, whenever if is a branch, it has more than one
    /// children.
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
        Iter::new(self)
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

impl<T: PartialEq<T>> PartialEq<Vector<T>> for Vector<T> {
    fn eq(&self, other: &Vector<T>) -> bool {
        self.length == other.length && self.iter().eq(other.iter())
    }
}

impl<T: Eq> Eq for Vector<T> {}

impl<T: PartialOrd<T>> PartialOrd<Vector<T>> for Vector<T>  {
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
            vector = vector.push(e);
        }

        vector
    }
}

pub struct Iter<'a, T: 'a> {
    vector: &'a Vector<T>,

    stack_forward: Option<Vec<IterStackElement<'a, T>>>,
    stack_backward: Option<Vec<IterStackElement<'a, T>>>,

    left_index: usize,  // inclusive
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
            Node::Leaf(_) => panic!("called current child of a branch"),
        }
    }

    fn current_elem(&self) -> &'a T {
        match *self.node {
            Node::Leaf(ref a) => a[self.index as usize].as_ref(),
            Node::Branch(_) => panic!("called current element of a branch"),
        }
    }

    #[inline]
    fn advance(&mut self, backwards: bool) -> () {
        self.index += if backwards { -1 } else { 1 };
    }

    #[inline]
    fn finished(&self) -> bool {
        self.index as usize >= self.node.used() || self.index < 0
    }
}

impl<'a, T> Iter<'a, T> {
    fn new(vector: &Vector<T>) -> Iter<T> {
        Iter {
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

        Iter::dig(stack, backwards);
    }

    fn init_if_needed(&mut self, backwards: bool) -> () {
        let stack_field = if backwards {
            &mut self.stack_backward
        } else {
            &mut self.stack_forward
        };

        if stack_field.is_none() {
            let mut stack: Vec<IterStackElement<T>> = Vec::with_capacity(self.vector.height() + 1);

            stack.push(IterStackElement::new(&*self.vector.root, backwards));

            Iter::dig(&mut stack, backwards);

            *stack_field = Some(stack);
        }
    }

    #[inline]
    fn current(stack: &Vec<IterStackElement<'a, T>>) -> Option<&'a T> {
        stack.last().map(|e| e.current_elem())
    }

    fn advance(stack: &mut Vec<IterStackElement<T>>, backwards: bool) -> () {
        match stack.pop() {
            Some(mut stack_element) => {
                stack_element.advance(backwards);

                if stack_element.finished() {
                    Iter::advance(stack, backwards);
                } else {
                    stack.push(stack_element);

                    Iter::dig(stack, backwards);
                }
            },
            None => (), // Reached the end.  Nothing to do.
        }
    }

    #[inline]
    fn non_empty(&self) -> bool {
        self.left_index < self.right_index
    }

    fn advance_forward(&mut self) -> () {
        if self.non_empty() {
            Iter::advance(self.stack_forward.as_mut().unwrap(), false);

            self.left_index += 1;
        }
    }

    fn current_forward(&self) -> Option<&'a T> {
        if self.non_empty() {
            Iter::current(self.stack_forward.as_ref().unwrap())
        } else {
            None
        }
    }

    fn advance_backward(&mut self) -> () {
        if self.non_empty() {
            Iter::advance(self.stack_backward.as_mut().unwrap(), true);

            self.right_index -= 1;
        }
    }

    fn current_backward(&self) -> Option<&'a T> {
        if self.non_empty() {
            Iter::current(self.stack_backward.as_ref().unwrap())
        } else {
            None
        }
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
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

impl<'a, T> DoubleEndedIterator for Iter<'a, T> {
    fn next_back(&mut self) -> Option<&'a T> {
        self.init_if_needed(true);

        let current = self.current_backward();

        self.advance_backward();

        current
    }
}

impl<'a, T> ExactSizeIterator for Iter<'a, T> {}

#[cfg(test)]
mod test;
