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
use std::iter::Peekable;

const DEFAULT_BITS: u8 = 5;

/// A persistent vector with structural sharing.  This data structure supports fast get, set,
/// and push.
///
/// # Complexity
///
/// Let *n* be the number of elements in the vector.
///
/// ## Temporal complexity
///
/// | Operation         | Best case | Average   | Worst case  |
/// |:----------------- | ---------:| ---------:| -----------:|
/// | new               |      Θ(1) |      Θ(1) |        Θ(1) |
/// | first/last/get    | Θ(log(n)) | Θ(log(n)) |   Θ(log(n)) |
/// | set               | Θ(log(n)) | Θ(log(n)) |   Θ(log(n)) |
/// | push              | Θ(log(n)) | Θ(log(n)) |   Θ(log(n)) |
/// | drop_last         | Θ(log(n)) | Θ(log(n)) |   Θ(log(n)) |
/// | clone             |      Θ(1) |      Θ(1) |        Θ(1) |
/// | iterator creation |      Θ(1) |      Θ(1) |        Θ(1) |
/// | iterator step     |      Θ(1) |      Θ(1) |   Θ(log(n)) |
/// | iterator full     |      Θ(n) |      Θ(n) |        Θ(n) |
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
    size: usize,
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

        match self {
            &Node::Branch(ref a) =>
                a[b].get(index, height - 1, bucket),
            &Node::Leaf(ref a) => {
                debug_assert!(height == 0);
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

        match self {
            &Node::Leaf(ref a) => {
                debug_assert!(height == 0, "Cannot have a leaf at this height");

                let mut a = a.clone();

                set_array(&mut a, b, Arc::new(value));

                Node::Leaf(a)
            },

            &Node::Branch(ref a) => {
                debug_assert!(height > 0, "Cannot have a branch at this height");

                let mut a = a.clone();

                let subtree: Node<T> = match a.get(b) {
                    Some(s) => (**s).clone(),
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

    fn is_empty(&self) -> bool {
        self.used() == 0
    }

    fn is_singleton(&self) -> bool {
        self.used() == 1
    }

    fn used(&self) -> usize {
        match self {
            &Node::Leaf(ref a)   => a.len(),
            &Node::Branch(ref a) => a.len(),
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

        let new_node: Node<T> = match self {
            &Node::Leaf(ref a) => {
                let mut new_a = a.clone();

                new_a.pop();

                Node::Leaf(new_a)
            },

            &Node::Branch(ref a) => {
                let mut new_a = a.clone();
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
        match self {
            &Node::Branch(ref a) => Node::Branch(a.clone()),
            &Node::Leaf(ref a)   => Node::Leaf(a.clone()),
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
            bits: bits,
            size: 0
        }
    }

    pub fn first(&self) -> Option<&T> {
        self.get(0)
    }

    pub fn last(&self) -> Option<&T> {
        match self.size {
            0 => None,
            n => self.get(n - 1),
        }
    }

    #[inline(always)]
    fn degree(&self) -> usize {
        1 << self.bits
    }

    fn height(&self) -> usize {
        let mut capacity = self.degree();
        let mut height = 0;

        while capacity < self.size {
            capacity <<= self.bits;
            height += 1;
        }

        height
    }

    #[inline(always)]
    fn mask(&self) -> usize {
        self.degree() - 1
    }

    #[inline(always)]
    fn bucket(&self, index: usize, height: usize) -> usize {
        (index >> (height * self.bits as usize)) & self.mask()
    }

    pub fn get(&self, index: usize) -> Option<&T> {
        if index >= self.size {
            None
        } else {
            Some(self.root.get(index, self.height(), |index, height| self.bucket(index, height)))
        }
    }

    pub fn set(&self, index: usize, v: T) -> Option<Vector<T>> {
        if index >= self.size {
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
        let adds_item: bool = index >= self.size;

        Vector {
            root: Arc::new(new_root),
            bits: self.bits,
            size: self.size + if adds_item { 1 } else { 0 },
        }
    }

    #[inline(always)]
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

    #[inline(always)]
    fn is_root_full(&self) -> bool {
        self.size == self.root_max_capacity()
    }

    pub fn push(&self, v: T) -> Vector<T> {
        if self.is_root_full() {
            let mut new_root: Node<T> = Node::new_empty_branch();

            match new_root {
                Node::Branch(ref mut values) => values.push(self.root.clone()),
                _ => unreachable!("expected a branch")
            }

            let new_vector = Vector {
                root: Arc::new(new_root),
                bits: self.bits,
                size: self.size + 1,
            };

            new_vector.assoc(self.size, v)
        } else  {
            self.assoc(self.size, v)
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
                        a[0].as_ref().clone()
                    } else {
                        unreachable!()
                    }
                } else {
                    branch
                }
        }
    }

    pub fn drop_last(&self) -> Option<Vector<T>> {
        if self.size == 0 {
            return None;
        }

        let new_vector = match self.root.drop_last() {
            None => Vector::new_with_bits(self.bits),
            Some(root) => {
                let new_root: Node<T> = Vector::compress_root(root);

                let new_vector = Vector {
                    root: Arc::new(new_root),
                    bits: self.bits,
                    size: self.size - 1,
                };

                new_vector
            }
        };

        Some(new_vector)
    }

    pub fn len(&self) -> usize {
        self.size
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
        self.size == other.size && self.iter().eq(other.iter())
    }

    fn ne(&self, other: &Vector<T>) -> bool {
        self.size != other.size || self.iter().ne(other.iter())
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
            root: self.root.clone(),
            bits: self.bits,
            size: self.size,
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

pub struct Iter<'a, T: 'a> {
    vector: &'a Vector<T>,

    stack_forward: Option<Vec<IterStackElement<'a, T>>>,
    stack_backward: Option<Vec<IterStackElement<'a, T>>>,

    left_index: usize,  // inclusive
    right_index: usize, // exclusive
}

struct IterStackElement<'a, T: 'a> {
    node: &'a Node<T>,
    index_iter: Peekable<Box<Iterator<Item=usize>>>,
}

impl<'a, T> IterStackElement<'a, T> {
    fn new(node: &Node<T>, backwards: bool) -> IterStackElement<T> {
        let ranges: Peekable<Box<Iterator<Item=usize>>> = {
            let r = 0..node.used();
            let range_iter: Box<Iterator<Item=usize>> =
                if backwards { Box::new(r.rev()) } else { Box::new(r) };

            range_iter.peekable()
        };

        IterStackElement {
            node: node,
            index_iter: ranges,
        }
    }

    #[inline(always)]
    fn current_node(&mut self) -> &'a Node<T> {
        match self.node {
            &Node::Branch(ref a) => a[*self.index_iter.peek().unwrap()].as_ref(),
            &Node::Leaf(_) => panic!("called current child of a branch"),
        }
    }

    #[inline(always)]
    fn current_elem(&mut self) -> &'a T {
        match self.node {
            &Node::Leaf(ref a) => a[*self.index_iter.peek().unwrap()].as_ref(),
            &Node::Branch(_) => panic!("called current element of a branch"),
        }
    }

    #[inline(always)]
    fn advance(&mut self) -> () {
        self.index_iter.next();
    }

    #[inline(always)]
    fn finished(&mut self) -> bool {
        self.index_iter.peek().is_none()
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
            let stack_top = stack.last_mut().unwrap();

            if let &Node::Leaf(_) = stack_top.node {
                return;
            }

            stack_top.current_node()
        };

        stack.push(IterStackElement::new(next_node, backwards));

        Iter::dig(stack, backwards);
    }

    #[inline(always)]
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

    #[inline(always)]
    fn current(stack: &mut Vec<IterStackElement<'a, T>>) -> Option<&'a T> {
        stack.last_mut().map(|e| e.current_elem())
    }

    fn advance(stack: &mut Vec<IterStackElement<T>>, backwards: bool) -> () {
        match stack.pop() {
            Some(mut stack_element) => {
                stack_element.advance();

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

    #[inline(always)]
    fn non_empty(&self) -> bool {
        self.left_index < self.right_index
    }

    #[inline(always)]
    fn advance_forward(&mut self) -> () {
        if self.non_empty() {
            Iter::advance(self.stack_forward.as_mut().unwrap(), false);

            self.left_index += 1;
        }
    }

    #[inline(always)]
    fn current_forward(&mut self) -> Option<&'a T> {
        if self.non_empty() {
            Iter::current(self.stack_forward.as_mut().unwrap())
        } else {
            None
        }
    }

    #[inline(always)]
    fn advance_backward(&mut self) -> () {
        if self.non_empty() {
            Iter::advance(self.stack_backward.as_mut().unwrap(), false);

            self.right_index -= 1;
        }
    }

    #[inline(always)]
    fn current_backward(&mut self) -> Option<&'a T> {
        if self.non_empty() {
            println!("ok");
            Iter::current(self.stack_backward.as_mut().unwrap())
        } else {
            println!("cant be");
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

impl<'a, T> IntoIterator for &'a Vector<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Iter<'a, T> {
        self.iter()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    mod node {
        use super::super::*;

        #[test]
        fn test_new_empty_branch() -> () {
            let node: Node<u32> = Node::new_empty_branch();

            match node {
                Node::Branch(a) => {
                    assert_eq!(a.len(), 0);
                    assert_eq!(a.capacity(), 0,
                        "Capacity of the branch array is wasteful");
                },
                _ => panic!("Invalid node type"),
            }
        }

        #[test]
        fn test_new_empty_leaf() -> () {
            let node: Node<u32> = Node::new_empty_leaf();

            match node {
                Node::Leaf(a) => {
                    assert_eq!(a.len(), 0);
                    assert_eq!(a.capacity(), 0,
                    "Capacity of the leaf array is wasteful");
                },
                _ => panic!("Invalid node type"),
            }
        }

        #[test]
        fn test_drop_last_single_level() -> () {
            let empty_leaf: Node<u32> = Node::new_empty_leaf();
            let empty_branch: Node<u32> = Node::new_empty_branch();
            let singleton_node: Node<u32> = Vector::new().push(0).root.as_ref().clone();
            let one_level_node: Node<u32> = Vector::new()
                .push(0).push(1).root.as_ref().clone();

            assert!(empty_leaf.drop_last().is_none());
            assert!(empty_branch.drop_last().is_none());
            assert!(singleton_node.drop_last().is_none());
            assert_eq!(one_level_node.drop_last().map(|n| n.used()), Some(1));
        }

        #[test]
        fn test_drop_last_multi_level() -> () {
            let node_three: Node<u32> = Vector::new_with_bits(1)
                .push(0).push(1).push(2).root.as_ref().clone();
            let node_four: Node<u32> = Vector::new_with_bits(1)
                .push(0).push(1).push(2).push(3).root.as_ref().clone();

            let node_three_after_drop = {
                let a_leaf = {
                    let mut a = Vec::with_capacity(2);
                    a.push(Arc::new(0));
                    a.push(Arc::new(1));
                    a
                };

                let leaf = Node::Leaf(a_leaf);

                let a_branch = {
                    let mut a = Vec::with_capacity(2);
                    a.push(Arc::new(leaf));
                    a
                };

                Node::Branch(a_branch)
            };

            let node_four_after_drop = {
                let a_leaf_0 = {
                    let mut a = Vec::with_capacity(2);
                    a.push(Arc::new(0));
                    a.push(Arc::new(1));
                    a
                };

                let leaf_0 = Node::Leaf(a_leaf_0);

                let a_leaf_1 = {
                    let mut a = Vec::with_capacity(2);
                    a.push(Arc::new(2));
                    a
                };

                let leaf_1 = Node::Leaf(a_leaf_1);

                let a_branch = {
                    let mut a = Vec::with_capacity(2);
                    a.push(Arc::new(leaf_0));
                    a.push(Arc::new(leaf_1));
                    a
                };

                Node::Branch(a_branch)
            };

            assert_eq!(node_three.drop_last(), Some(node_three_after_drop));
            assert_eq!(node_four.drop_last(), Some(node_four_after_drop));
        }

        // test clone keeps capazity
    }

    fn dummy_vector_with_size(size: usize) -> Vector<u8> {
        let mut v = Vector::new_with_bits(5);
        v.size = size;
        v
    }

    #[test]
    fn test_degree() -> () {
        assert_eq!(Vector::<u8>::new_with_bits(1).degree(),  2);
        assert_eq!(Vector::<u8>::new_with_bits(2).degree(),  4);
        assert_eq!(Vector::<u8>::new_with_bits(3).degree(),  8);
        assert_eq!(Vector::<u8>::new_with_bits(4).degree(), 16);
        assert_eq!(Vector::<u8>::new_with_bits(5).degree(), 32);
    }

    #[test]
    fn test_height() -> () {
        assert_eq!(dummy_vector_with_size(      0).height(), 0);
        assert_eq!(dummy_vector_with_size(      5).height(), 0);
        assert_eq!(dummy_vector_with_size(     32).height(), 0);
        assert_eq!(dummy_vector_with_size(     33).height(), 1);
        assert_eq!(dummy_vector_with_size(     64).height(), 1);
        assert_eq!(dummy_vector_with_size(    128).height(), 1);
        assert_eq!(dummy_vector_with_size(    512).height(), 1);
        assert_eq!(dummy_vector_with_size(   1024).height(), 1);
        assert_eq!(dummy_vector_with_size(   1025).height(), 2);
        assert_eq!(dummy_vector_with_size(   1025).height(), 2);
        assert_eq!(dummy_vector_with_size(  32768).height(), 2);
        assert_eq!(dummy_vector_with_size(  32769).height(), 3);
        assert_eq!(dummy_vector_with_size(1048576).height(), 3);
        assert_eq!(dummy_vector_with_size(1048577).height(), 4);
    }

    #[test]
    fn test_mask() -> () {
        assert_eq!(Vector::<u8>::new_with_bits(1).mask(), 0b00001);
        assert_eq!(Vector::<u8>::new_with_bits(2).mask(), 0b00011);
        assert_eq!(Vector::<u8>::new_with_bits(3).mask(), 0b00111);
        assert_eq!(Vector::<u8>::new_with_bits(4).mask(), 0b01111);
        assert_eq!(Vector::<u8>::new_with_bits(5).mask(), 0b11111);
    }

    #[test]
    fn test_bucket() -> () {
        assert_eq!(Vector::<u8>::new_with_bits(5).bucket(0b00100_00011_00010_00001, 0), 0b00001);
        assert_eq!(Vector::<u8>::new_with_bits(5).bucket(0b00100_00011_00010_00001, 1), 0b00010);
        assert_eq!(Vector::<u8>::new_with_bits(5).bucket(0b00100_00011_00010_00001, 2), 0b00011);
        assert_eq!(Vector::<u8>::new_with_bits(5).bucket(0b00100_00011_00010_00001, 3), 0b00100);
    }

    #[test]
    fn test_push_adds_element() -> () {
        let limit = 32*32*32+1;
        let mut vector: Vector<i32> = Vector::new();

        for i in 0..limit {
            vector = vector.push(-i);
            assert_eq!(vector.get(i as usize), Some(&-i));
        }
    }

    #[test]
    fn test_push_maintains_size() -> () {
        let limit = 128;
        let mut vector: Vector<i32> = Vector::new();

        for i in 0..limit {
            assert_eq!(vector.len(), i as usize);
            vector = vector.push(-i);
        }

        assert_eq!(vector.len(), limit as usize);
    }

    #[test]
    fn test_compress_root() -> () {
        let empty_leaf: Node<u32> = Node::new_empty_leaf();
        let empty_branch: Node<u32> = Node::new_empty_branch();
        let singleton_leaf: Node<u32> = Vector::new().push(0).root.as_ref().clone();
        let compressed_branch: Node<u32> = Vector::new_with_bits(1)
            .push(0).push(1).push(3).root.as_ref().clone();
        let (uncompressed_branch, uncompressed_branch_leaf) = {
            let leaf = Vector::new_with_bits(1)
                .push(0).push(1).root.as_ref().clone();

            let a_branch = {
                let mut a = Vec::with_capacity(2);
                a.push(Arc::new(leaf.clone()));
                a
            };

            (Node::Branch(a_branch), leaf)
        };

        assert_eq!(empty_leaf.clone(), Vector::compress_root(empty_leaf));
        assert_eq!(empty_branch.clone(), Vector::compress_root(empty_branch));
        assert_eq!(singleton_leaf.clone(), Vector::compress_root(singleton_leaf));
        assert_eq!(compressed_branch.clone(), Vector::compress_root(compressed_branch));
        assert_eq!(uncompressed_branch_leaf, Vector::compress_root(uncompressed_branch));
    }

    #[test]
    fn test_drop_left_drops_last_element() -> () {
        let limit = 4*4*4*4+1;
        let mut vector: Vector<i32> = Vector::new_with_bits(2);
        let mut vectors = Vec::with_capacity(limit);

        for i in 0..limit {
            vector = vector.push(2 * i as i32);
            vectors.push(vector.clone())
        }

        for _ in 0..limit {
            let v = vectors.pop().unwrap();
            assert_eq!(vector, v);
            vector = vector.drop_last().unwrap();
        }

        assert_eq!(vector, Vector::new());
    }

    #[test]
    fn test_drop_left_keeps_vector_consistent() -> () {
        let limit = 4*4*4*4*4*4+1;
        let mut vector: Vector<i32> = Vector::new_with_bits(2);

        for i in 0..limit {
            vector = vector.push(2 * i as i32);
        }

        for _ in 0..(limit / (4 * 4)) {
            vector = vector.drop_last().unwrap();
        }

        let new_len = limit - limit / (4 * 4);

        for i in 0..new_len {
            assert_eq!(vector.get(i).unwrap(), &(2 * i as i32));
        }

        assert_eq!(vector.get(new_len as usize), None);
    }

    #[test]
    fn test_drop_last_maintains_size() -> () {
        let limit = 128;
        let mut vector: Vector<i32> = Vector::new();

        for i in 0..limit {
            vector = vector.push(-i);
        }

        for i in 0..limit {
            assert_eq!(vector.len(), (limit - i) as usize);
            vector = vector.drop_last().unwrap();
        }

        assert_eq!(vector.len(), 0);
    }

    #[test]
    fn test_drop_last_on_empty_vector() -> () {
        let vector: Vector<i32> = Vector::new();

        assert_eq!(vector.drop_last(), None);
    }

    #[test]
    fn test_set_overwrites() -> () {
        let limit = 32*32+1;
        let mut vector: Vector<i32> = Vector::new();

        for i in 0..limit {
            vector = vector.push(-i);
        }

        vector = vector.set(834, 0).unwrap();

        assert_eq!(vector.get(833), Some(&-833));
        assert_eq!(vector.get(834), Some(&0));
        assert_eq!(vector.get(835), Some(&-835));
        assert_eq!(vector.get(limit as usize), None);
    }

    #[test]
    fn test_set_maintains_size() -> () {
        let limit = 32*32*32*1;
        let mut vector: Vector<i32> = Vector::new();

        for i in 0..limit {
            vector = vector.push(-i);
        }

        for i in 0..limit {
            vector = vector.set(i as usize, i * i).unwrap();
            assert_eq!(vector.len(), limit as usize);
        }
    }

    #[test]
    fn test_set_out_of_bounds() -> () {
        let empty_vector: Vector<i32> = Vector::new();
        let singleton_vector: Vector<i32> = Vector::new().push(0);

        assert_eq!(empty_vector.set(0, 0), None);
        assert_eq!(singleton_vector.set(1, 0), None);
    }

    #[test]
    fn test_root_max_capacity() -> () {
        assert_eq!(dummy_vector_with_size(    0).root_max_capacity(),      32);
        assert_eq!(dummy_vector_with_size(    5).root_max_capacity(),      32);
        assert_eq!(dummy_vector_with_size(   32).root_max_capacity(),      32);
        assert_eq!(dummy_vector_with_size(   33).root_max_capacity(),    1024);
        assert_eq!(dummy_vector_with_size( 1024).root_max_capacity(),    1024);
        assert_eq!(dummy_vector_with_size( 1025).root_max_capacity(),   32768);
        assert_eq!(dummy_vector_with_size(32768).root_max_capacity(),   32768);
        assert_eq!(dummy_vector_with_size(32769).root_max_capacity(), 1048576);
    }

    #[test]
    fn test_is_root_full() -> () {
        assert!(!dummy_vector_with_size(    0).is_root_full());
        assert!(!dummy_vector_with_size(    5).is_root_full());
        assert!( dummy_vector_with_size(   32).is_root_full());
        assert!(!dummy_vector_with_size(   33).is_root_full());
        assert!( dummy_vector_with_size( 1024).is_root_full());
        assert!(!dummy_vector_with_size( 1025).is_root_full());
        assert!( dummy_vector_with_size(32768).is_root_full());
        assert!(!dummy_vector_with_size(32769).is_root_full());
    }

    #[test]
    fn test_get() -> () {
        let limit = 32*32*32+1;
        let mut vector = Vector::new();

        for i in 0..limit {
            vector = vector.push(i + 1);
        }

        assert_eq!(vector.get(0), Some(&1));
        assert_eq!(vector.get(2020), Some(&2021));
        assert_eq!(vector.get(limit - 1), Some(&limit));
        assert_eq!(vector.get(limit), None);
    }

    #[test]
    fn test_index() -> () {
        let vector = Vector::new()
            .push(10)
            .push(11)
            .push(12);

        assert_eq!(vector[0], 10);
        assert_eq!(vector[1], 11);
        assert_eq!(vector[2], 12);
    }

    #[test]
    fn test_first() -> () {
        let empty_vector: Vector<i32> = Vector::new();
        let vector = Vector::new()
            .push(1);

        assert_eq!(empty_vector.first(), None);
        assert_eq!(vector.first(), Some(&1));
    }

    #[test]
    fn test_last() -> () {
        let empty_vector: Vector<i32> = Vector::new();
        let vector = Vector::new()
            .push(1)
            .push(2);

        assert_eq!(empty_vector.last(), None);
        assert_eq!(vector.last(), Some(&2));
    }

    #[test]
    fn test_iter_empty_vector() -> () {
        let vector: Vector<i32> = Vector::new();

        for _ in vector.iter() {
            panic!("iterator should be empty");
        }
    }

    #[test]
    fn test_iter_big_vector() -> () {
        let limit = 32*32*32+1;
        let mut vector = Vector::new();
        let mut expected = 0;
        let mut left = limit;

        for i in 0..limit {
            vector = vector.push(i);
        }

        for v in vector.iter() {
            left -= 1;

            assert!(left >= 0);
            assert_eq!(*v, expected);

            expected += 1;
        }

        assert_eq!(left, 0);
    }


    #[test]
    fn test_iter_backwards() -> () {
        let vector = Vector::new()
            .push(0)
            .push(1)
            .push(2)
            .push(3);
        let mut expected = 3;
        let mut left = 4;

        for n in vector.iter().rev() {
            left -= 1;

            assert!(left >= 0);
            assert_eq!(*n, expected);

            expected -= 1;
        }

        assert_eq!(left, 0);
    }

    #[test]
    fn test_iter_both_directions() -> () {
        let vector = Vector::new()
            .push(0)
            .push(1)
            .push(2)
            .push(3)
            .push(4)
            .push(5);
        let mut iterator = vector.iter();

        assert_eq!(iterator.next(),      Some(&0));
        assert_eq!(iterator.next_back(), Some(&5));
        assert_eq!(iterator.next_back(), Some(&4));
        assert_eq!(iterator.next(),      Some(&1));
        assert_eq!(iterator.next(),      Some(&2));
        assert_eq!(iterator.next_back(), Some(&3));
        assert_eq!(iterator.next_back(), None);
        assert_eq!(iterator.next(),      None);
    }

    #[test]
    fn test_iter_size_hint() -> () {
        let vector = Vector::new()
            .push(0)
            .push(1)
            .push(2);
        let mut iterator = vector.iter();

        assert_eq!(iterator.size_hint(), (3, Some(3)));

        iterator.next();

        assert_eq!(iterator.size_hint(), (2, Some(2)));

        iterator.next_back();

        assert_eq!(iterator.size_hint(), (1, Some(1)));

        iterator.next_back();

        assert_eq!(iterator.size_hint(), (0, Some(0)));
    }

    #[test]
    fn test_into_iterator() -> () {
        let vector = Vector::new()
            .push(0)
            .push(1)
            .push(2)
            .push(3);
        let mut expected = 0;
        let mut left = 4;

        for n in &vector {
            left -= 1;

            assert!(left >= 0);
            assert_eq!(*n, expected);

            expected += 1;
        }

        assert_eq!(left, 0);
    }

    #[test]
    fn test_default() -> () {
        let vector: Vector<i32> = Vector::default();

        assert_eq!(vector.len(), 0);
    }

    #[test]
    fn test_display() -> () {
        let empty_vector: Vector<i32> = Vector::new();
        let singleton_vector = Vector::new()
            .push("hello");
        let vector = Vector::new()
            .push(0)
            .push(1)
            .push(2)
            .push(3);

        assert_eq!(format!("{}", empty_vector), "[]");
        assert_eq!(format!("{}", singleton_vector), "[hello]");
        assert_eq!(format!("{}", vector), "[0, 1, 2, 3]");
    }

    #[test]
    fn test_eq() -> () {
        let vector_1 = Vector::new()
            .push("a")
            .push("a");
        let vector_1_prime = Vector::new()
            .push("a")
            .push("a");
        let vector_2 = Vector::new()
            .push("a")
            .push("b");
        let vector_3 = Vector::new()
            .push("a")
            .push("b")
            .push("c");

        assert_ne!(vector_1, vector_2);
        assert_ne!(vector_2, vector_3);
        assert_eq!(vector_1, vector_1);
        assert_eq!(vector_1, vector_1_prime);
        assert_eq!(vector_2, vector_2);

        // We also use check this since `assert_ne!()` does not call `ne`.
        assert!(vector_1.ne(&vector_2));
        assert!(vector_2.ne(&vector_3));
    }

    #[test]
    fn test_partial_ord() -> () {
        let vector_1 = Vector::new()
            .push("a");
        let vector_1_prime = Vector::new()
            .push("a");
        let vector_2 = Vector::new()
            .push("b");
        let vector_3 = Vector::new()
            .push(0.0);
        let vector_4 = Vector::new()
            .push(::std::f32::NAN);

        assert_eq!(vector_1.partial_cmp(&vector_1_prime), Some(Ordering::Equal));
        assert_eq!(vector_1.partial_cmp(&vector_2), Some(Ordering::Less));
        assert_eq!(vector_2.partial_cmp(&vector_1), Some(Ordering::Greater));
        assert_eq!(vector_3.partial_cmp(&vector_4), None);
    }

    #[test]
    fn test_ord() -> () {
        let vector_1 = Vector::new()
            .push("a");
        let vector_1_prime = Vector::new()
            .push("a");
        let vector_2 = Vector::new()
            .push("b");

        assert_eq!(vector_1.cmp(&vector_1_prime), Ordering::Equal);
        assert_eq!(vector_1.cmp(&vector_2), Ordering::Less);
        assert_eq!(vector_2.cmp(&vector_1), Ordering::Greater);
    }

    fn hash<T: Hash>(vector: &Vector<T>) -> u64 {
        let mut hasher = ::std::collections::hash_map::DefaultHasher::new();

        vector.hash(&mut hasher);

        hasher.finish()
    }

    #[test]
    fn test_hash() -> () {
        let vector_1 = Vector::new()
            .push("a");
        let vector_1_prime = Vector::new()
            .push("a");
        let vector_2 = Vector::new()
            .push("a")
            .push("b");

        assert_eq!(hash(&vector_1), hash(&vector_1));
        assert_eq!(hash(&vector_1), hash(&vector_1_prime));
        assert_ne!(hash(&vector_1), hash(&vector_2));
    }

    #[test]
    fn test_clone() -> () {
        let vector = Vector::new()
            .push("hello")
            .push("there");
        let clone = vector.clone();

        assert_eq!(clone.len(), vector.len());
        assert!(clone.iter().eq(vector.iter()));
    }

    #[test]
    fn compile_time_test_is_send() -> () {
        let vector: Box<Send> = Box::new(Vector::<i32>::new());

        ::std::mem::drop(vector);
    }

    #[test]
    fn compile_time_test_is_sync() -> () {
        let vector: Box<Sync> = Box::new(Vector::<i32>::new());

        ::std::mem::drop(vector);
    }
}
