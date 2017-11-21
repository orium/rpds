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

use std::sync::Arc;
use std::fmt::Display;
use std::cmp::Ordering;
use std::hash::{Hasher, Hash};
use std::borrow::Borrow;
use std::iter::FromIterator;

/// A persistent list with structural sharing.  This data structure supports fast `push_front()`,
/// `drop_first()`, `first()`, and `last()`.
///
/// # Complexity
///
/// Let *n* be the number of elements in the list.
///
/// ## Temporal complexity
///
/// | Operation         | Best case | Average | Worst case  |
/// |:----------------- | ---------:| -------:| -----------:|
/// | `new()`           |      Θ(1) |    Θ(1) |        Θ(1) |
/// | `push_front()`    |      Θ(1) |    Θ(1) |        Θ(1) |
/// | `drop_first()`    |      Θ(1) |    Θ(1) |        Θ(1) |
/// | `first()`         |      Θ(1) |    Θ(1) |        Θ(1) |
/// | `last()`          |      Θ(1) |    Θ(1) |        Θ(1) |
/// | `len()`           |      Θ(1) |    Θ(1) |        Θ(1) |
/// | `clone()`         |      Θ(1) |    Θ(1) |        Θ(1) |
/// | iterator creation |      Θ(1) |    Θ(1) |        Θ(1) |
/// | iterator step     |      Θ(1) |    Θ(1) |        Θ(1) |
/// | iterator full     |      Θ(n) |    Θ(n) |        Θ(n) |
///
/// ## Space complexity
///
/// The space complexity is *Θ(n)*.
///
/// # Implementation details
///
/// This is your classic functional list with "cons" and "nil" nodes.
#[derive(Debug)]
pub struct List<T> {
    node: Arc<Node<T>>,
    last: Option<Arc<T>>,
    length: usize,
}

#[derive(Debug)]
enum Node<T> {
    Cons(Arc<T>, Arc<Node<T>>),
    Nil,
}

impl<T> List<T> {
    pub fn new() -> List<T> {
        List {
            node: Arc::new(Node::Nil),
            last: None,
            length: 0,
        }
    }

    pub fn first(&self) -> Option<&T> {
        match *self.node {
            Node::Cons(ref h, _) => Some(h),
            Node::Nil            => None,
        }
    }

    pub fn last(&self) -> Option<&T> {
        match self.last {
            Some(ref v) => Some(v.borrow()),
            None        => None,
        }
    }

    pub fn drop_first(&self) -> Option<List<T>> {
        match *self.node {
            Node::Cons(_, ref t) => {
                let new_length = self.length - 1;
                let new_list = List {
                    node: Arc::clone(t),
                    last: if new_length == 0 { None } else { self.last.clone() },
                    length: new_length
                };

                Some(new_list)
            },
            Node::Nil => None,
        }
    }

    pub fn push_front(&self, v: T) -> List<T> {
        let value = Arc::new(v);

        List {
            // TODO With non-lexical lifetimes can we put the "last" after "node"?
            last: {
                match self.last {
                    Some(ref v) => Some(Arc::clone(v)),
                    None        => Some(Arc::clone(&value)),
                }
            },
            node: Arc::new(Node::Cons(value, Arc::clone(&self.node))),
            length: self.length + 1,
        }
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

impl<T> Default for List<T> {
    fn default() -> List<T> {
        List::new()
    }
}

impl<T: PartialEq> PartialEq for List<T> {
    fn eq(&self, other: &List<T>) -> bool {
        self.length == other.length && self.iter().eq(other.iter())
    }
}

impl<T: Eq> Eq for List<T> {}

impl<T: PartialOrd<T>> PartialOrd<List<T>> for List<T>  {
    fn partial_cmp(&self, other: &List<T>) -> Option<Ordering> {
        self.iter().partial_cmp(other.iter())
    }
}

impl<T: Ord> Ord for List<T> {
    fn cmp(&self, other: &List<T>) -> Ordering {
        self.iter().cmp(other.iter())
    }
}

impl<T: Hash> Hash for List<T> {
    fn hash<H: Hasher>(&self, state: &mut H) -> () {
        for e in self {
            e.hash(state);
        }
    }
}

impl<T> Clone for List<T> {
    fn clone(&self) -> List<T> {
        List {
            node: Arc::clone(&self.node),
            last: self.last.clone(),
            length: self.length,
        }
    }
}

impl<T: Display> Display for List<T> {
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

impl<'a, T> IntoIterator for &'a List<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Iter<'a, T> {
        self.iter()
    }
}

impl<T> FromIterator<T> for List<T> {
    fn from_iter<I: IntoIterator<Item = T>>(into_iter: I) -> List<T> {
        let iter = into_iter.into_iter();
        let (min_size, max_size_hint) = iter.size_hint();
        let mut vec: Vec<T> = Vec::with_capacity(max_size_hint.unwrap_or(min_size));

        for e in iter {
            vec.push(e);
        }

        let mut list: List<T> = List::new();

        for e in vec.into_iter().rev() {
            list = list.push_front(e);
        }

        list
    }
}

#[derive(Debug)]
pub struct Iter<'a, T: 'a> {
    next: &'a Node<T>,
    length: usize,
}

impl<'a, T> Iter<'a, T> {
    fn new(list: &List<T>) -> Iter<T> {
        Iter {
            next: list.node.borrow(),
            length: list.len(),
        }
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        match *self.next {
            Node::Cons(ref v, ref t) => {
                self.next = t;
                self.length -= 1;
                Some(v)
            },
            Node::Nil => None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.length, Some(self.length))
    }
}

impl<'a, T> ExactSizeIterator for Iter<'a, T> {}

#[cfg(test)]
mod test;
