/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use std::cmp::Ordering;
use std::hash::{Hasher, Hash};
use std::iter::FromIterator;
use std::fmt::Display;
use sequence::list;
use List;

#[cfg(feature = "serde")]
use serde::ser::{Serialize, Serializer, SerializeSeq};
#[cfg(feature = "serde")]
use serde::de::{Deserialize, Deserializer};

// TODO Use impl trait for return value when available
pub type Iter<'a, T> = list::Iter<'a, T>;

/// A persistent stack with structural sharing.  This data structure supports fast `push()`,
/// `pop()`, and `peek()`.
///
/// # Complexity
///
/// Let *n* be the number of elements in the stack.
///
/// ## Temporal complexity
///
/// | Operation         | Best case | Average | Worst case  |
/// |:----------------- | ---------:| -------:| -----------:|
/// | `new()`           |      Θ(1) |    Θ(1) |        Θ(1) |
/// | `push()`          |      Θ(1) |    Θ(1) |        Θ(1) |
/// | `pop()`           |      Θ(1) |    Θ(1) |        Θ(1) |
/// | `peek()`          |      Θ(1) |    Θ(1) |        Θ(1) |
/// | `size()`          |      Θ(1) |    Θ(1) |        Θ(1) |
/// | `clone()`         |      Θ(1) |    Θ(1) |        Θ(1) |
/// | iterator creation |      Θ(1) |    Θ(1) |        Θ(1) |
/// | iterator step     |      Θ(1) |    Θ(1) |        Θ(1) |
/// | iterator full     |      Θ(n) |    Θ(n) |        Θ(n) |
///
/// # Implementation details
///
/// This is a thin wrapper around a [List](../sequence/list/struct.List.html).
#[derive(Debug)]
pub struct Stack<T> {
    list: List<T>
}

impl<T> Stack<T> {
    pub fn new() -> Stack<T> {
        Stack {
            list: List::new()
        }
    }

    pub fn peek(&self) -> Option<&T> {
        self.list.first()
    }

    pub fn pop(&self) -> Option<Stack<T>> {
        self.list.drop_first().map(|l| Stack { list: l } )
    }

    pub fn push(&self, v: T) -> Stack<T> {
        Stack {
            list: self.list.push_front(v)
        }
    }

    #[inline]
    pub fn size(&self) -> usize {
        self.list.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.size() == 0
    }

    pub fn iter(&self) -> Iter<T> {
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
    fn hash<H: Hasher>(&self, state: &mut H) -> () {
        self.list.hash(state)
    }
}

impl<T> Clone for Stack<T> {
    fn clone(&self) -> Stack<T> {
        Stack {
            list: List::clone(&self.list)
        }
    }
}

impl<T: Display> Display for Stack<T> {
    fn fmt(&self, fmt: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
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
            list: List::from_iter(into_iter)
        }
    }
}

#[cfg(feature = "serde")]
impl<T> Serialize for Stack<T> where T: Serialize {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut state = serializer.serialize_seq(Some(self.list.len()))?;
        for item in self {
            state.serialize_element(&item)?;
        }
        state.end()
    }
}

#[cfg(feature = "serde")]
impl<'de, T> Deserialize<'de> for Stack<T> where T: Deserialize<'de> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let list: List<T> = Deserialize::deserialize(deserializer)?;
        Ok(Stack {
            list: list,
        })
    }
}


#[cfg(test)]
mod test;
