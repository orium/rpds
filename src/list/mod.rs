/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use alloc::vec::Vec;
use archery::*;
use core::borrow::Borrow;
use core::cmp::Ordering;
use core::fmt::Display;
use core::hash::{Hash, Hasher};
use core::iter::FromIterator;

// TODO Use impl trait instead of this when available.
pub type Iter<'a, T, P> = core::iter::Map<IterPtr<'a, T, P>, fn(&SharedPointer<T, P>) -> &T>;

#[doc(hidden)]
#[macro_export]
macro_rules! list_reverse {
    ($ptr_kind:ty ; ; $($reversed:expr),*) => {
         {
            #[allow(unused_mut)]
            let mut l: List<_, $ptr_kind> = $crate::List::new_with_ptr_kind();
            $(
                l.push_front_mut($reversed);
            )*
            l
         }
    };
    ($ptr_kind:ty ; $h:expr ; $($reversed:expr),*) => {
        $crate::list_reverse!($ptr_kind ; ; $h, $($reversed),*)
    };
    ($ptr_kind:ty ; $h:expr, $($t:expr),+ ; $($reversed:expr),*) => {
        $crate::list_reverse!($ptr_kind ; $($t),* ; $h, $($reversed),*)
    };

    // This is just to handle the cases where this macro is called with an extra comma in the
    // reserve list, which can happen in a recursive call.
    ($ptr_kind:ty ; $($t:expr),* ; $($reversed:expr),*,) => {
        $crate::list_reverse!($ptr_kind ; $($t),* ; $($reversed),*)
    };
}

/// Creates a [`List`](crate::List) containing the given arguments:
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
        $crate::list_reverse!(::archery::RcK ; $($e),* ; )
    };
}

/// Creates a [`List`](crate::List) that implements `Sync`, containing the given arguments:
///
/// ```
/// # use rpds::*;
/// #
/// let l = List::new_sync()
///     .push_front(3)
///     .push_front(2)
///     .push_front(1);
///
/// assert_eq!(list_sync![1, 2, 3], l);
///
/// fn is_sync() -> impl Sync {
///     list_sync![0, 1, 1, 2, 3, 5, 8]
/// }
/// ```
#[macro_export]
macro_rules! list_sync {
    ($($e:expr),*) => {
        $crate::list_reverse!(::archery::ArcTK ; $($e),* ; )
    };
}

/// A persistent list with structural sharing.
///
/// # Complexity
///
/// Let *n* be the number of elements in the list.
///
/// ## Temporal complexity
///
/// | Operation         | Average | Worst case  |
/// |:----------------- | -------:| -----------:|
/// | `new()`           |    Θ(1) |        Θ(1) |
/// | `push_front()`    |    Θ(1) |        Θ(1) |
/// | `drop_first()`    |    Θ(1) |        Θ(1) |
/// | `reverse()`       |    Θ(n) |        Θ(n) |
/// | `first()`         |    Θ(1) |        Θ(1) |
/// | `last()`          |    Θ(1) |        Θ(1) |
/// | `len()`           |    Θ(1) |        Θ(1) |
/// | `clone()`         |    Θ(1) |        Θ(1) |
/// | iterator creation |    Θ(1) |        Θ(1) |
/// | iterator step     |    Θ(1) |        Θ(1) |
/// | iterator full     |    Θ(n) |        Θ(n) |
///
/// # Implementation details
///
/// This is your classic functional list with "cons" and "nil" nodes, with a little extra sauce to
/// make some operations more efficient.
#[derive(Debug)]
pub struct List<T, P = RcK>
where
    P: SharedPointerKind,
{
    head: Option<SharedPointer<Node<T, P>, P>>,
    last: Option<SharedPointer<T, P>>,
    length: usize,
}

#[derive(Debug)]
struct Node<T, P>
where
    P: SharedPointerKind,
{
    value: SharedPointer<T, P>,
    next: Option<SharedPointer<Node<T, P>, P>>,
}

impl<T, P> Clone for Node<T, P>
where
    P: SharedPointerKind,
{
    fn clone(&self) -> Node<T, P> {
        Node { value: SharedPointer::clone(&self.value), next: self.next.clone() }
    }
}

pub type ListSync<T> = List<T, ArcTK>;

impl<T> ListSync<T> {
    #[must_use]
    pub fn new_sync() -> ListSync<T> {
        List::new_with_ptr_kind()
    }
}

impl<T> List<T> {
    #[must_use]
    pub fn new() -> List<T> {
        List::new_with_ptr_kind()
    }
}

impl<T, P> List<T, P>
where
    P: SharedPointerKind,
{
    #[must_use]
    pub fn new_with_ptr_kind() -> List<T, P> {
        List { head: None, last: None, length: 0 }
    }

    #[must_use]
    pub fn first(&self) -> Option<&T> {
        self.head.as_ref().map(|node| node.value.borrow())
    }

    #[must_use]
    pub fn last(&self) -> Option<&T> {
        self.last.as_ref().map(Borrow::borrow)
    }

    #[must_use]
    pub fn drop_first(&self) -> Option<List<T, P>> {
        let mut new_list = self.clone();

        if new_list.drop_first_mut() { Some(new_list) } else { None }
    }

    pub fn drop_first_mut(&mut self) -> bool {
        self.head.take().is_some_and(|h| {
            self.head.clone_from(&h.next);
            self.length -= 1;

            if self.length == 0 {
                self.last = None;
            }

            true
        })
    }

    fn push_front_ptr_mut(&mut self, v: SharedPointer<T, P>) {
        if self.length == 0 {
            self.last = Some(SharedPointer::clone(&v));
        }

        let new_head = Node { value: v, next: self.head.take() };

        self.head = Some(SharedPointer::new(new_head));
        self.length += 1;
    }

    #[must_use]
    pub fn push_front(&self, v: T) -> List<T, P> {
        let mut new_list = self.clone();

        new_list.push_front_mut(v);

        new_list
    }

    pub fn push_front_mut(&mut self, v: T) {
        self.push_front_ptr_mut(SharedPointer::new(v));
    }

    #[must_use]
    pub fn reverse(&self) -> List<T, P> {
        let mut new_list = List::new_with_ptr_kind();

        // It is significantly faster to re-implement this here than to clone and call
        // `reverse_mut()`.  The reason is that since this is a linear data structure all nodes will
        // need to be cloned given that the ref count would be greater than one.

        for v in self.iter_ptr() {
            new_list.push_front_ptr_mut(SharedPointer::clone(v));
        }

        new_list
    }

    pub fn reverse_mut(&mut self) {
        self.last = self.head.as_ref().map(|next| SharedPointer::clone(&next.value));

        let mut prev: Option<SharedPointer<Node<T, P>, P>> = None;
        let mut current: Option<SharedPointer<Node<T, P>, P>> = self.head.take();

        while let Some(mut curr_ptr) = current {
            let curr = SharedPointer::make_mut(&mut curr_ptr);
            let curr_next = curr.next.take();

            curr.next = prev.take();

            current = curr_next;
            prev = Some(curr_ptr);
        }

        self.head = prev;
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
    pub(crate) fn iter_ptr(&self) -> IterPtr<'_, T, P> {
        IterPtr::new(self)
    }
}

impl<T, P> List<T, P>
where
    T: Clone,
    P: SharedPointerKind,
{
    #[must_use]
    pub(crate) fn first_mut(&mut self) -> Option<&mut T> {
        self.head
            .as_mut()
            .map(|node| SharedPointer::make_mut(&mut SharedPointer::make_mut(node).value))
    }
}

impl<T, P> Default for List<T, P>
where
    P: SharedPointerKind,
{
    fn default() -> List<T, P> {
        List::new_with_ptr_kind()
    }
}

impl<T: PartialEq, P, PO> PartialEq<List<T, PO>> for List<T, P>
where
    P: SharedPointerKind,
    PO: SharedPointerKind,
{
    fn eq(&self, other: &List<T, PO>) -> bool {
        self.length == other.length && self.iter().eq(other.iter())
    }
}

impl<T: Eq, P> Eq for List<T, P> where P: SharedPointerKind {}

impl<T: PartialOrd<T>, P, PO> PartialOrd<List<T, PO>> for List<T, P>
where
    P: SharedPointerKind,
    PO: SharedPointerKind,
{
    fn partial_cmp(&self, other: &List<T, PO>) -> Option<Ordering> {
        self.iter().partial_cmp(other.iter())
    }
}

impl<T: Ord, P> Ord for List<T, P>
where
    P: SharedPointerKind,
{
    fn cmp(&self, other: &List<T, P>) -> Ordering {
        self.iter().cmp(other.iter())
    }
}

impl<T: Hash, P> Hash for List<T, P>
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

impl<T, P> Clone for List<T, P>
where
    P: SharedPointerKind,
{
    fn clone(&self) -> List<T, P> {
        List { head: self.head.clone(), last: self.last.clone(), length: self.length }
    }
}

impl<T: Display, P> Display for List<T, P>
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

impl<'a, T, P> IntoIterator for &'a List<T, P>
where
    P: SharedPointerKind,
{
    type Item = &'a T;
    type IntoIter = Iter<'a, T, P>;

    fn into_iter(self) -> Iter<'a, T, P> {
        self.iter()
    }
}

impl<T, P> FromIterator<T> for List<T, P>
where
    P: SharedPointerKind,
{
    fn from_iter<I: IntoIterator<Item = T>>(into_iter: I) -> List<T, P> {
        let iter = into_iter.into_iter();
        let (min_size, max_size_hint) = iter.size_hint();
        let mut vec: Vec<T> = Vec::with_capacity(max_size_hint.unwrap_or(min_size));

        for e in iter {
            vec.push(e);
        }

        let mut list: List<T, P> = List::new_with_ptr_kind();

        for e in vec.into_iter().rev() {
            list.push_front_mut(e);
        }

        list
    }
}

// Drop the list iteratively to prevent stack overflow.
impl<T, P> Drop for List<T, P>
where
    P: SharedPointerKind,
{
    fn drop(&mut self) {
        let mut head = self.head.take();
        while let Some(node) = head {
            match SharedPointer::try_unwrap(node) {
                Ok(mut node) => {
                    head = node.next.take();
                }
                _ => {
                    break;
                }
            }
        }
    }
}

#[derive(Debug)]
pub struct IterPtr<'a, T, P>
where
    P: SharedPointerKind,
{
    next: Option<&'a Node<T, P>>,
    length: usize,
}

impl<T, P> IterPtr<'_, T, P>
where
    P: SharedPointerKind,
{
    fn new(list: &List<T, P>) -> IterPtr<'_, T, P> {
        IterPtr { next: list.head.as_ref().map(AsRef::as_ref), length: list.len() }
    }
}

impl<'a, T, P> Iterator for IterPtr<'a, T, P>
where
    P: SharedPointerKind,
{
    type Item = &'a SharedPointer<T, P>;

    fn next(&mut self) -> Option<&'a SharedPointer<T, P>> {
        match self.next {
            Some(Node { value: v, next: t }) => {
                self.next = t.as_ref().map(AsRef::as_ref);
                self.length -= 1;
                Some(v)
            }
            None => None,
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.length, Some(self.length))
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

    impl<T, P> Serialize for List<T, P>
    where
        T: Serialize,
        P: SharedPointerKind,
    {
        fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
            serializer.collect_seq(self)
        }
    }

    impl<'de, T, P> Deserialize<'de> for List<T, P>
    where
        T: Deserialize<'de>,
        P: SharedPointerKind,
    {
        fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<List<T, P>, D::Error> {
            deserializer
                .deserialize_seq(ListVisitor { _phantom_t: PhantomData, _phantom_p: PhantomData })
        }
    }

    struct ListVisitor<T, P> {
        _phantom_t: PhantomData<T>,
        _phantom_p: PhantomData<P>,
    }

    impl<'de, T, P> Visitor<'de> for ListVisitor<T, P>
    where
        T: Deserialize<'de>,
        P: SharedPointerKind,
    {
        type Value = List<T, P>;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            formatter.write_str("a sequence")
        }

        fn visit_seq<A>(self, mut seq: A) -> Result<List<T, P>, A::Error>
        where
            A: SeqAccess<'de>,
        {
            let mut vec: Vec<T> = if let Some(capacity) = seq.size_hint() {
                Vec::with_capacity(capacity)
            } else {
                Vec::new()
            };

            while let Some(value) = seq.next_element()? {
                vec.push(value);
            }

            let mut list: List<T, P> = List::new_with_ptr_kind();

            for value in vec.into_iter().rev() {
                list.push_front_mut(value);
            }

            Ok(list)
        }
    }
}

#[cfg(test)]
mod test;
