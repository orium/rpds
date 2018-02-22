/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use std::sync::Arc;
use std::fmt::Display;
use std::cmp::Ordering;
use std::hash::{Hasher, Hash};
use std::borrow::Borrow;
use std::iter::FromIterator;

// TODO Use impl trait instead of this when available.
pub type Iter<'a, T> = ::std::iter::Map<IterArc<'a, T>, fn(&Arc<T>) -> &T>;

#[doc(hidden)]
#[macro_export]
macro_rules! list_reverse {
    ( ; $($reversed:expr),*) => {
         {
            #[allow(unused_mut)]
            let mut l = $crate::List::new();
            $(
                l = l.push_front($reversed);
            )*
            l
        }
    };
    ($h:expr ; $($reversed:expr),*) => {
        list_reverse!( ; $h, $($reversed),*)
    };
    ($h:expr, $($t:expr),+ ; $($reversed:expr),*) => {
        list_reverse!($($t),* ; $h, $($reversed),*)
    };

    // This is just to handle the cases where this macro is called with an extra comma in the
    // reserve list, which can happen in a recursive call.
    ($($t:expr),* ; $($reversed:expr),*,) => {
        list_reverse!($($t),* ; $($reversed),*)
    };
}

/// Creates a [`List`](sequence/list/struct.List.html) containing the given arguments:
///
/// ```
/// # use rpds::*;
/// #
/// let l = List::new()
///     .push_front(3)
///     .push_front(2)
///     .push_front(1);
///
/// assert_eq!(list![1, 2, 3], l);
/// ```
#[macro_export]
macro_rules! list {
    ($($e:expr),*) => {
        list_reverse!($($e),* ; )
    };
}

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
/// | `reverse()`       |      Θ(n) |    Θ(n) |        Θ(n) |
/// | `first()`         |      Θ(1) |    Θ(1) |        Θ(1) |
/// | `last()`          |      Θ(1) |    Θ(1) |        Θ(1) |
/// | `len()`           |      Θ(1) |    Θ(1) |        Θ(1) |
/// | `clone()`         |      Θ(1) |    Θ(1) |        Θ(1) |
/// | iterator creation |      Θ(1) |    Θ(1) |        Θ(1) |
/// | iterator step     |      Θ(1) |    Θ(1) |        Θ(1) |
/// | iterator full     |      Θ(n) |    Θ(n) |        Θ(n) |
///
/// # Implementation details
///
/// This is your classic functional list with "cons" and "nil" nodes, with a little extra sauce to
/// make some operations more efficient.
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
        self.last.as_ref().map(|v| v.borrow())
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

    fn push_front_arc(&self, v: Arc<T>) -> List<T> {
        List {
            // TODO With non-lexical lifetimes can we put the "last" after "node"?
            last: {
                match self.last {
                    Some(ref v) => Some(Arc::clone(v)),
                    None        => Some(Arc::clone(&v)),
                }
            },
            node: Arc::new(Node::Cons(v, Arc::clone(&self.node))),
            length: self.length + 1,
        }
    }

    pub fn push_front(&self, v: T) -> List<T> {
        self.push_front_arc(Arc::new(v))
    }

    pub fn reverse(&self) -> List<T> {
        let mut list = List::new();

        for v in self.iter_arc() {
            list = list.push_front_arc(Arc::clone(v));
        }

        list
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

    pub(crate) fn iter_arc(&self) -> IterArc<T> {
        IterArc::new(self)
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

impl<T: PartialOrd<T>> PartialOrd<List<T>> for List<T> {
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
        // Add the hash of length so that if two collections are added one after the other it doesn't
        // hash to the same thing as a single collection with the same elements in the same order.
        self.len().hash(state);

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
pub struct IterArc<'a, T: 'a> {
    next: &'a Node<T>,
    length: usize,
}

impl<'a, T> IterArc<'a, T> {
    fn new(list: &List<T>) -> IterArc<T> {
        IterArc {
            next:   list.node.borrow(),
            length: list.len(),
        }
    }
}

impl<'a, T> Iterator for IterArc<'a, T> {
    type Item = &'a Arc<T>;

    fn next(&mut self) -> Option<&'a Arc<T>> {
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

impl<'a, T> ExactSizeIterator for IterArc<'a, T> {}

#[cfg(feature = "serde")]
pub mod serde {
    use super::*;
    use serde::ser::{Serialize, Serializer};
    use serde::de::{Deserialize, Deserializer, SeqAccess, Visitor};
    use std::marker::PhantomData;
    use std::fmt;

    impl<T> Serialize for List<T>
        where T: Serialize {
        fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
            serializer.collect_seq(self)
        }
    }

    impl<'de, T> Deserialize<'de> for List<T> where T: Deserialize<'de> {
        fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<List<T>, D::Error> {
            deserializer.deserialize_seq(ListVisitor { phantom: PhantomData } )
        }
    }

    struct ListVisitor<T> {
        phantom: PhantomData<T>
    }

    impl<'de, T> Visitor<'de> for ListVisitor<T>
        where T: Deserialize<'de> {
        type Value = List<T>;

        fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
            formatter.write_str("a sequence")
        }

        fn visit_seq<A>(self, mut seq: A) -> Result<List<T>, A::Error>
            where A: SeqAccess<'de> {
            let mut vec: Vec<T> = if let Some(capacity) = seq.size_hint() {
                    Vec::with_capacity(capacity)
                } else {
                    Vec::new()
                };

            while let Some(value) = seq.next_element()? {
                vec.push(value);
            }

            let mut list: List<T> = List::new();

            for value in vec.into_iter().rev() {
                list = list.push_front(value);
            }

            Ok(list)
        }
    }
}

#[cfg(test)]
mod test;
