/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use crate::List;
use archery::*;
use core::cmp::Ordering;
use core::fmt::Display;
use core::hash::{Hash, Hasher};
use core::iter::FromIterator;

// TODO Use impl trait for return value when available
pub type Iter<'a, T, P> = crate::list::Iter<'a, T, P>;

/// Creates a [`Stack`](crate::Stack) containing the given arguments:
///
/// ```
/// # use rpds::*;
/// #
/// let mut s = Stack::new()
///     .push(1)
///     .push(2)
///     .push(3);
///
/// assert_eq!(stack![1, 2, 3], s);
/// ```
#[macro_export]
macro_rules! stack {
    ($($e:expr),*) => {
        {
            #[allow(unused_mut)]
            let mut s = $crate::Stack::new();
            $(
                s.push_mut($e);
            )*
            s
        }
    };
}

/// Creates a [`Stack`](crate::Stack) that implements `Sync`, containing the given arguments:
///
/// ```
/// # use rpds::*;
/// #
/// let mut s = Stack::new_sync()
///     .push(1)
///     .push(2)
///     .push(3);
///
/// assert_eq!(stack_sync![1, 2, 3], s);
///
/// fn is_sync() -> impl Sync {
///     stack_sync![0, 1, 1, 2, 3, 5, 8]
/// }
/// ```
#[macro_export]
macro_rules! stack_sync {
    ($($e:expr),*) => {
        {
            #[allow(unused_mut)]
            let mut s = $crate::Stack::new_sync();
            $(
                s.push_mut($e);
            )*
            s
        }
    };
}

/// A persistent stack with structural sharing.
///
/// # Complexity
///
/// Let *n* be the number of elements in the stack.
///
/// ## Temporal complexity
///
/// | Operation         | Average | Worst case  |
/// |:----------------- | -------:| -----------:|
/// | `new()`           |    Θ(1) |        Θ(1) |
/// | `push()`          |    Θ(1) |        Θ(1) |
/// | `pop()`           |    Θ(1) |        Θ(1) |
/// | `peek()`          |    Θ(1) |        Θ(1) |
/// | `size()`          |    Θ(1) |        Θ(1) |
/// | `clone()`         |    Θ(1) |        Θ(1) |
/// | iterator creation |    Θ(1) |        Θ(1) |
/// | iterator step     |    Θ(1) |        Θ(1) |
/// | iterator full     |    Θ(n) |        Θ(n) |
///
/// # Implementation details
///
/// This is a thin wrapper around a [`List`](crate::List).
#[derive(Debug)]
pub struct Stack<T, P = RcK>
where
    P: SharedPointerKind,
{
    list: List<T, P>,
}

pub type StackSync<T> = Stack<T, ArcTK>;

impl<T> StackSync<T> {
    #[must_use]
    pub fn new_sync() -> StackSync<T> {
        Stack::new_with_ptr_kind()
    }
}

impl<T> Stack<T> {
    #[must_use]
    pub fn new() -> Stack<T> {
        Stack::new_with_ptr_kind()
    }
}

impl<T, P> Stack<T, P>
where
    P: SharedPointerKind,
{
    #[must_use]
    pub fn new_with_ptr_kind() -> Stack<T, P> {
        Stack { list: List::new_with_ptr_kind() }
    }

    #[must_use]
    pub fn peek(&self) -> Option<&T> {
        self.list.first()
    }

    #[must_use]
    pub fn pop(&self) -> Option<Stack<T, P>> {
        let mut new_stack = self.clone();

        if new_stack.pop_mut() { Some(new_stack) } else { None }
    }

    pub fn pop_mut(&mut self) -> bool {
        self.list.drop_first_mut()
    }

    #[must_use]
    pub fn push(&self, v: T) -> Stack<T, P> {
        let mut new_stack = self.clone();

        new_stack.push_mut(v);

        new_stack
    }

    pub fn push_mut(&mut self, v: T) {
        self.list.push_front_mut(v);
    }

    #[must_use]
    #[inline]
    pub fn size(&self) -> usize {
        self.list.len()
    }

    #[must_use]
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.list.is_empty()
    }

    pub fn iter(&self) -> Iter<'_, T, P> {
        self.list.iter()
    }
}

impl<T, P> Default for Stack<T, P>
where
    P: SharedPointerKind,
{
    fn default() -> Stack<T, P> {
        Stack::new_with_ptr_kind()
    }
}

impl<T: PartialEq, P, PO> PartialEq<Stack<T, PO>> for Stack<T, P>
where
    P: SharedPointerKind,
    PO: SharedPointerKind,
{
    fn eq(&self, other: &Stack<T, PO>) -> bool {
        self.list.eq(&other.list)
    }
}

impl<T: Eq, P> Eq for Stack<T, P> where P: SharedPointerKind {}

impl<T: PartialOrd<T>, P, PO> PartialOrd<Stack<T, PO>> for Stack<T, P>
where
    P: SharedPointerKind,
    PO: SharedPointerKind,
{
    fn partial_cmp(&self, other: &Stack<T, PO>) -> Option<Ordering> {
        self.list.partial_cmp(&other.list)
    }
}

impl<T: Ord, P> Ord for Stack<T, P>
where
    P: SharedPointerKind,
{
    fn cmp(&self, other: &Stack<T, P>) -> Ordering {
        self.list.cmp(&other.list)
    }
}

impl<T: Hash, P> Hash for Stack<T, P>
where
    P: SharedPointerKind,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.list.hash(state);
    }
}

impl<T, P> Clone for Stack<T, P>
where
    P: SharedPointerKind,
{
    fn clone(&self) -> Stack<T, P> {
        Stack { list: List::clone(&self.list) }
    }
}

impl<T: Display, P> Display for Stack<T, P>
where
    P: SharedPointerKind,
{
    fn fmt(&self, fmt: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let mut first = true;

        fmt.write_str("Stack(")?;

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

impl<'a, T, P> IntoIterator for &'a Stack<T, P>
where
    P: SharedPointerKind,
{
    type Item = &'a T;
    type IntoIter = Iter<'a, T, P>;

    fn into_iter(self) -> Iter<'a, T, P> {
        self.list.iter()
    }
}

impl<T, P> FromIterator<T> for Stack<T, P>
where
    P: SharedPointerKind,
{
    fn from_iter<I: IntoIterator<Item = T>>(into_iter: I) -> Stack<T, P> {
        Stack { list: List::from_iter(into_iter) }
    }
}

#[cfg(feature = "serde")]
pub mod serde {
    use super::*;
    use ::serde::de::{Deserialize, Deserializer};
    use ::serde::ser::{Serialize, Serializer};

    impl<T, P> Serialize for Stack<T, P>
    where
        T: Serialize,
        P: SharedPointerKind,
    {
        fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
            self.list.serialize(serializer)
        }
    }

    impl<'de, T, P> Deserialize<'de> for Stack<T, P>
    where
        T: Deserialize<'de>,
        P: SharedPointerKind,
    {
        fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Stack<T, P>, D::Error> {
            Deserialize::deserialize(deserializer).map(|list| Stack { list })
        }
    }
}

#[cfg(test)]
mod test;
