/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use crate::List;
use alloc::vec::Vec;
use archery::*;
use core::borrow::Borrow;
use core::cmp::Ordering;
use core::fmt::Display;
use core::hash::{Hash, Hasher};
use core::iter::FromIterator;

// TODO Use impl trait instead of this when available.
type IterPtr<'a, T, P> =
    core::iter::Chain<crate::list::IterPtr<'a, T, P>, LazilyReversedListIter<'a, T, P>>;
pub type Iter<'a, T, P> = core::iter::Map<IterPtr<'a, T, P>, fn(&SharedPointer<T, P>) -> &T>;

/// Creates a [`Queue`](crate::Queue) containing the given arguments:
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
                q.enqueue_mut($e);
            )*
            q
        }
    };
}

/// Creates a [`Queue`](crate::Queue) that implements `Sync`, containing the given arguments:
///
/// ```
/// # use rpds::*;
/// #
/// let q = Queue::new_sync()
///     .enqueue(1)
///     .enqueue(2)
///     .enqueue(3);
///
/// assert_eq!(queue_sync![1, 2, 3], q);
///
/// fn is_sync() -> impl Sync {
///     queue_sync![0, 1, 3]
/// }
/// ```
#[macro_export]
macro_rules! queue_sync {
    ($($e:expr),*) => {
        {
            #[allow(unused_mut)]
            let mut q = $crate::Queue::new_sync();
            $(
                q.enqueue_mut($e);
            )*
            q
        }
    };
}

/// A persistent queue with structural sharing.
///
/// # Complexity
///
/// Let *n* be the number of elements in the queue.
///
/// ## Temporal complexity
///
/// | Operation             | Average | Worst case  |
/// |:--------------------- | -------:| -----------:|
/// | `new()`               |    Θ(1) |        Θ(1) |
/// | `enqueue()`           |    Θ(1) |        Θ(1) |
/// | `dequeue()`           |    Θ(1) |        Θ(n) |
/// | `dequeue()` amortized |    Θ(1) |        Θ(1) |
/// | `peek()`              |    Θ(1) |        Θ(1) |
/// | `len()`               |    Θ(1) |        Θ(1) |
/// | `clone()`             |    Θ(1) |        Θ(1) |
/// | iterator creation     |    Θ(1) |        Θ(1) |
/// | iterator step         |    Θ(1) |        Θ(n) |
/// | iterator full         |    Θ(n) |        Θ(n) |
///
/// # Implementation details
///
/// This queue is implemented as described in
/// [Immutability in C# Part Four: An Immutable Queue](https://goo.gl/hWyMuS).
#[derive(Debug)]
pub struct Queue<T, P = RcK>
where
    P: SharedPointerKind,
{
    in_list: List<T, P>,
    out_list: List<T, P>,
}

pub type QueueSync<T> = Queue<T, ArcTK>;

impl<T> QueueSync<T> {
    #[must_use]
    pub fn new_sync() -> QueueSync<T> {
        Queue::new_with_ptr_kind()
    }
}

impl<T> Queue<T> {
    #[must_use]
    pub fn new() -> Queue<T> {
        Queue::new_with_ptr_kind()
    }
}

impl<T, P> Queue<T, P>
where
    P: SharedPointerKind,
{
    #[must_use]
    pub fn new_with_ptr_kind() -> Queue<T, P> {
        Queue { in_list: List::new_with_ptr_kind(), out_list: List::new_with_ptr_kind() }
    }

    #[must_use]
    pub fn peek(&self) -> Option<&T> {
        if !self.out_list.is_empty() { self.out_list.first() } else { self.in_list.last() }
    }

    #[must_use]
    pub fn dequeue(&self) -> Option<Queue<T, P>> {
        let mut new_queue = self.clone();

        if new_queue.dequeue_mut() { Some(new_queue) } else { None }
    }

    pub fn dequeue_mut(&mut self) -> bool {
        if !self.out_list.is_empty() {
            self.out_list.drop_first_mut();
            true
        } else if !self.in_list.is_empty() {
            core::mem::swap(&mut self.in_list, &mut self.out_list);

            self.out_list.reverse_mut();
            self.out_list.drop_first_mut();
            true
        } else {
            false
        }
    }

    #[must_use]
    pub fn enqueue(&self, v: T) -> Queue<T, P> {
        let mut new_queue = self.clone();

        new_queue.enqueue_mut(v);

        new_queue
    }

    pub fn enqueue_mut(&mut self, v: T) {
        self.in_list.push_front_mut(v);
    }

    #[must_use]
    #[inline]
    pub fn len(&self) -> usize {
        self.in_list.len() + self.out_list.len()
    }

    #[must_use]
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn iter(&self) -> Iter<'_, T, P> {
        self.iter_ptr().map(|v| v.borrow())
    }

    fn iter_ptr(&self) -> IterPtr<'_, T, P> {
        self.out_list.iter_ptr().chain(LazilyReversedListIter::new(&self.in_list))
    }
}

impl<T, P> Default for Queue<T, P>
where
    P: SharedPointerKind,
{
    fn default() -> Queue<T, P> {
        Queue::new_with_ptr_kind()
    }
}

impl<T: PartialEq, P, PO> PartialEq<Queue<T, PO>> for Queue<T, P>
where
    P: SharedPointerKind,
    PO: SharedPointerKind,
{
    fn eq(&self, other: &Queue<T, PO>) -> bool {
        self.len() == other.len() && self.iter().eq(other.iter())
    }
}

impl<T: Eq, P> Eq for Queue<T, P> where P: SharedPointerKind {}

impl<T: PartialOrd<T>, P, PO> PartialOrd<Queue<T, PO>> for Queue<T, P>
where
    P: SharedPointerKind,
    PO: SharedPointerKind,
{
    fn partial_cmp(&self, other: &Queue<T, PO>) -> Option<Ordering> {
        self.iter().partial_cmp(other.iter())
    }
}

impl<T: Ord, P> Ord for Queue<T, P>
where
    P: SharedPointerKind,
{
    fn cmp(&self, other: &Queue<T, P>) -> Ordering {
        self.iter().cmp(other.iter())
    }
}

impl<T: Hash, P> Hash for Queue<T, P>
where
    P: SharedPointerKind,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Add the hash of length so that if two collections are added one after the other it
        // doesn't hash to the same thing as a single collection with the same elements in the same
        // order.
        self.len().hash(state);

        for e in self {
            e.hash(state);
        }
    }
}

impl<T, P> Clone for Queue<T, P>
where
    P: SharedPointerKind,
{
    fn clone(&self) -> Queue<T, P> {
        Queue { in_list: self.in_list.clone(), out_list: self.out_list.clone() }
    }
}

impl<T: Display, P> Display for Queue<T, P>
where
    P: SharedPointerKind,
{
    fn fmt(&self, fmt: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let mut first = true;

        fmt.write_str("Queue(")?;

        for v in self {
            if !first {
                fmt.write_str(", ")?;
            }
            v.fmt(fmt)?;
            first = false;
        }

        fmt.write_str(")")
    }
}

impl<'a, T, P> IntoIterator for &'a Queue<T, P>
where
    P: SharedPointerKind,
{
    type Item = &'a T;
    type IntoIter = Iter<'a, T, P>;

    fn into_iter(self) -> Iter<'a, T, P> {
        self.iter()
    }
}

impl<T, P> FromIterator<T> for Queue<T, P>
where
    P: SharedPointerKind,
{
    fn from_iter<I: IntoIterator<Item = T>>(into_iter: I) -> Queue<T, P> {
        Queue { out_list: List::from_iter(into_iter), in_list: List::new_with_ptr_kind() }
    }
}

pub enum LazilyReversedListIter<'a, T: 'a, P>
where
    P: SharedPointerKind,
{
    Uninitialized { list: &'a List<T, P> },
    Initialized { vec: Vec<&'a SharedPointer<T, P>>, current: Option<usize> },
}

impl<T, P> LazilyReversedListIter<'_, T, P>
where
    P: SharedPointerKind,
{
    fn new(list: &List<T, P>) -> LazilyReversedListIter<'_, T, P> {
        LazilyReversedListIter::Uninitialized { list }
    }
}

impl<'a, T, P> Iterator for LazilyReversedListIter<'a, T, P>
where
    P: SharedPointerKind,
{
    type Item = &'a SharedPointer<T, P>;

    fn next(&mut self) -> Option<&'a SharedPointer<T, P>> {
        match self {
            LazilyReversedListIter::Uninitialized { list } => {
                let len = list.len();
                let mut vec: Vec<&'a SharedPointer<T, P>> = Vec::with_capacity(len);

                for v in list.iter_ptr() {
                    vec.push(v);
                }

                *self = LazilyReversedListIter::Initialized {
                    vec,
                    current: if len > 0 { Some(len - 1) } else { None },
                };

                self.next()
            }

            &mut LazilyReversedListIter::Initialized { ref vec, ref mut current } => {
                let v = current.map(|i| vec[i]);

                *current = match *current {
                    Some(0) => None,
                    Some(i) => Some(i - 1),
                    None => None,
                };

                v
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = match self {
            LazilyReversedListIter::Uninitialized { list } => list.len(),
            LazilyReversedListIter::Initialized { current: Some(i), .. } => i + 1,
            LazilyReversedListIter::Initialized { current: None, .. } => 0,
        };

        (len, Some(len))
    }
}

impl<T, P> ExactSizeIterator for LazilyReversedListIter<'_, T, P> where P: SharedPointerKind {}

#[cfg(feature = "serde")]
pub mod serde {
    use super::*;
    use ::serde::de::{Deserialize, Deserializer};
    use ::serde::ser::{Serialize, Serializer};

    impl<T, P> Serialize for Queue<T, P>
    where
        T: Serialize,
        P: SharedPointerKind,
    {
        fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
            serializer.collect_seq(self)
        }
    }

    impl<'de, T, P> Deserialize<'de> for Queue<T, P>
    where
        T: Deserialize<'de>,
        P: SharedPointerKind,
    {
        fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Queue<T, P>, D::Error> {
            Deserialize::deserialize(deserializer)
                .map(|list| Queue { out_list: list, in_list: List::new_with_ptr_kind() })
        }
    }
}

#[cfg(test)]
mod test;
