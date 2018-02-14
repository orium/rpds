/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use std::sync::Arc;
use std::fmt::Display;
use std::cmp::Ordering;
use std::hash::{Hasher, Hash};
use std::iter::FromIterator;
use std::borrow::Borrow;
use sequence::list;
use List;

// TODO Use impl trait instead of this when available.
pub type IterArc<'a, T> = ::std::iter::Chain<list::IterArc<'a, T>, LazilyReversedListIter<'a, T>>;
pub type Iter<'a, T> = ::std::iter::Map<IterArc<'a, T>, fn(&Arc<T>) -> &T>;

/// Creates a [`Queue`](queue/struct.Queue.html) containing the given arguments:
///
/// ```
/// # use rpds::*;
/// #
/// let q = Queue::new()
///     .enqueue(1)
///     .enqueue(2)
///     .enqueue(3);
///
/// assert_eq!(queue![1, 2, 3], q);
/// ```
#[macro_export]
macro_rules! queue {
    ($($e:expr),*) => {
        {
            #[allow(unused_mut)]
            let mut q = $crate::Queue::new();
            $(
                q = q.enqueue($e);
            )*
            q
        }
    };
}

/// A persistent queue with structural sharing.  This data structure supports fast `enqueue()`,
/// `dequeue()`, and `peek()`.
///
/// # Complexity
///
/// Let *n* be the number of elements in the queue.
///
/// ## Temporal complexity
///
/// | Operation             | Best case | Average | Worst case  |
/// |:--------------------- | ---------:| -------:| -----------:|
/// | `new()`               |      Θ(1) |    Θ(1) |        Θ(1) |
/// | `enqueue()`           |      Θ(1) |    Θ(1) |        Θ(1) |
/// | `dequeue()`           |      Θ(1) |    Θ(1) |        Θ(n) |
/// | `dequeue()` amortized |      Θ(1) |    Θ(1) |        Θ(1) |
/// | `peek()`              |      Θ(1) |    Θ(1) |        Θ(1) |
/// | `len()`               |      Θ(1) |    Θ(1) |        Θ(1) |
/// | `clone()`             |      Θ(1) |    Θ(1) |        Θ(1) |
/// | iterator creation     |      Θ(1) |    Θ(1) |        Θ(1) |
/// | iterator step         |      Θ(1) |    Θ(1) |        Θ(n) |
/// | iterator full         |      Θ(n) |    Θ(n) |        Θ(n) |
///
/// # Implementation details
///
/// This queue is implemented as described in
/// [Immutability in C# Part Four: An Immutable Queue](https://blogs.msdn.microsoft.com/ericlippert/2007/12/10/immutability-in-c-part-four-an-immutable-queue/).
#[derive(Debug)]
pub struct Queue<T> {
    in_list:  List<T>,
    out_list: List<T>,
}

impl<T> Queue<T> {
    pub fn new() -> Queue<T> {
        Queue {
            in_list: List::new(),
            out_list: List::new(),
        }
    }

    pub fn peek(&self) -> Option<&T> {
        if !self.out_list.is_empty() {
            self.out_list.first()
        } else {
            self.in_list.last()
        }
    }

    pub fn dequeue(&self) -> Option<Queue<T>> {
        if !self.out_list.is_empty() {
            Some(
                Queue {
                    in_list:  self.in_list.clone(),
                    out_list: self.out_list.drop_first().unwrap(),
                }
            )
        } else if !self.in_list.is_empty() {
            Some(
                Queue {
                    in_list:  List::new(),
                    out_list: self.in_list.reverse().drop_first().unwrap(),
                }
            )
        } else {
            None
        }
    }

    pub fn enqueue(&self, v: T) -> Queue<T> {
        Queue {
            in_list:  self.in_list.push_front(v),
            out_list: self.out_list.clone(),
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.in_list.len() + self.out_list.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn iter(&self) -> Iter<T> {
        self.iter_arc().map(|v| v.borrow())
    }

    fn iter_arc(&self) -> IterArc<T> {
        self.out_list.iter_arc().chain(LazilyReversedListIter::new(&self.in_list))
    }
}

impl<T> Default for Queue<T> {
    fn default() -> Queue<T> {
        Queue::new()
    }
}

impl<T: PartialEq> PartialEq for Queue<T> {
    fn eq(&self, other: &Queue<T>) -> bool {
        self.len() == other.len() && self.iter().eq(other.iter())
    }
}

impl<T: Eq> Eq for Queue<T> {}

impl<T: PartialOrd<T>> PartialOrd<Queue<T>> for Queue<T> {
    fn partial_cmp(&self, other: &Queue<T>) -> Option<Ordering> {
        self.iter().partial_cmp(other.iter())
    }
}

impl<T: Ord> Ord for Queue<T> {
    fn cmp(&self, other: &Queue<T>) -> Ordering {
        self.iter().cmp(other.iter())
    }
}

impl<T: Hash> Hash for Queue<T> {
    fn hash<H: Hasher>(&self, state: &mut H) -> () {
        // Add the hash of length so that if two collections are added one after the other it doesn't
        // hash to the same thing as a single collection with the same elements in the same order.
        self.len().hash(state);

        for e in self {
            e.hash(state);
        }
    }
}

impl<T> Clone for Queue<T> {
    fn clone(&self) -> Queue<T> {
        Queue {
            in_list:  self.in_list.clone(),
            out_list: self.out_list.clone(),
        }
    }
}

impl<T: Display> Display for Queue<T> {
    fn fmt(&self, fmt: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        let mut first = true;

        fmt.write_str("Queue(")?;

        for v in self.iter() {
            if !first {
                fmt.write_str(", ")?;
            }
            v.fmt(fmt)?;
            first = false;
        }

        fmt.write_str(")")
    }
}

impl<'a, T> IntoIterator for &'a Queue<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Iter<'a, T> {
        self.iter()
    }
}

impl<T> FromIterator<T> for Queue<T> {
    fn from_iter<I: IntoIterator<Item = T>>(into_iter: I) -> Queue<T> {
        Queue {
            out_list: List::from_iter(into_iter),
            in_list:  List::new(),
        }
    }
}

pub enum LazilyReversedListIter<'a, T: 'a> {
    Uninitialized { list: &'a List<T> },
    Initialized { vec: Vec<&'a Arc<T>>, current: Option<usize> },
}

impl<'a, T> LazilyReversedListIter<'a, T> {
    fn new(list: &List<T>) -> LazilyReversedListIter<T> {
        LazilyReversedListIter::Uninitialized { list }
    }
}

impl<'a, T> Iterator for LazilyReversedListIter<'a, T> {
    type Item = &'a Arc<T>;

    fn next(&mut self) -> Option<&'a Arc<T>> {
        match *self {
            LazilyReversedListIter::Uninitialized { list } => {
                let len = list.len();
                let mut vec: Vec<&'a Arc<T>> = Vec::with_capacity(len);

                for v in list.iter_arc() {
                    vec.push(v);
                }

                *self = LazilyReversedListIter::Initialized {
                    vec,
                    current: if len > 0 { Some(len - 1) } else { None },
                };

                self.next()
            },

            LazilyReversedListIter::Initialized { ref vec, ref mut current } => {
                let v = current.map(|i| vec[i]);

                *current = match *current {
                    Some(0) => None,
                    Some(i) => Some(i - 1),
                    None    => None,
                };

                v
            },
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = match *self {
            LazilyReversedListIter::Uninitialized { list } => list.len(),
            LazilyReversedListIter::Initialized { current: Some(i), .. } => i + 1,
            LazilyReversedListIter::Initialized { current: None, .. }    => 0,
        };

        (len, Some(len))
    }
}

impl<'a, T> ExactSizeIterator for LazilyReversedListIter<'a, T> {}

#[cfg(feature = "serde")]
pub mod serde {
    use super::*;
    use serde::ser::{Serialize, Serializer};
    use serde::de::{Deserialize, Deserializer};

    impl<T> Serialize for Queue<T>
        where T: Serialize {
        fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
            serializer.collect_seq(self)
        }
    }

    impl<'de, T> Deserialize<'de> for Queue<T>
        where T: Deserialize<'de> {
        fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Queue<T>, D::Error> {
            let list: List<T> = Deserialize::deserialize(deserializer)?;
            Ok(Queue {
                out_list: list,
                in_list:  List::new(),
            })
        }
    }
}

#[cfg(test)]
mod test;
