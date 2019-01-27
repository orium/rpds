/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use crate::List;
use std::cmp::Ordering;
use std::fmt::Display;
use std::hash::{Hash, Hasher};
use std::iter::FromIterator;

// TODO Use impl trait for return value when available
pub type Iter<'a, T> = crate::list::Iter<'a, T>;

/// Creates a [`Stack`](stack/struct.Stack.html) containing the given arguments:
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
/// This is a thin wrapper around a [`List`](../list/struct.List.html).
#[derive(Debug)]
pub struct Stack<T> {
    list: List<T>,
}

impl<T> Stack<T> {
    #[must_use]
    pub fn new() -> Stack<T> {
        Stack { list: List::new() }
    }

    #[must_use]
    pub fn peek(&self) -> Option<&T> {
        self.list.first()
    }

    #[must_use]
    pub fn pop(&self) -> Option<Stack<T>> {
        let mut new_stack = self.clone();

        if new_stack.pop_mut() {
            Some(new_stack)
        } else {
            None
        }
    }

    pub fn pop_mut(&mut self) -> bool {
        self.list.drop_first_mut()
    }

    #[must_use]
    pub fn push(&self, v: T) -> Stack<T> {
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

    #[must_use]
    pub fn iter(&self) -> Iter<'_, T> {
        self.list.iter()
    }
}

impl<T> Default for Stack<T> {
    fn default() -> Stack<T> {
        Stack::new()
    }
}

impl<T: PartialEq> PartialEq for Stack<T> {
    fn eq(&self, other: &Stack<T>) -> bool {
        self.list.eq(&other.list)
    }
}

impl<T: Eq> Eq for Stack<T> {}

impl<T: PartialOrd<T>> PartialOrd<Stack<T>> for Stack<T> {
    fn partial_cmp(&self, other: &Stack<T>) -> Option<Ordering> {
        self.list.partial_cmp(&other.list)
    }
}

impl<T: Ord> Ord for Stack<T> {
    fn cmp(&self, other: &Stack<T>) -> Ordering {
        self.list.cmp(&other.list)
    }
}

impl<T: Hash> Hash for Stack<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.list.hash(state)
    }
}

impl<T> Clone for Stack<T> {
    fn clone(&self) -> Stack<T> {
        Stack {
            list: List::clone(&self.list),
        }
    }
}

impl<T: Display> Display for Stack<T> {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut first = true;

        fmt.write_str("Stack(")?;

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

impl<'a, T> IntoIterator for &'a Stack<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Iter<'a, T> {
        self.list.iter()
    }
}

impl<T> FromIterator<T> for Stack<T> {
    fn from_iter<I: IntoIterator<Item = T>>(into_iter: I) -> Stack<T> {
        Stack {
            list: List::from_iter(into_iter),
        }
    }
}

#[cfg(feature = "serde")]
pub mod serde {
    use super::*;
    use ::serde::de::{Deserialize, Deserializer};
    use ::serde::ser::{Serialize, Serializer};

    impl<T> Serialize for Stack<T>
    where
        T: Serialize,
    {
        fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
            self.list.serialize(serializer)
        }
    }

    impl<'de, T> Deserialize<'de> for Stack<T>
    where
        T: Deserialize<'de>,
    {
        fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Stack<T>, D::Error> {
            Deserialize::deserialize(deserializer).map(|list| Stack { list })
        }
    }
}

#[cfg(test)]
mod test;
