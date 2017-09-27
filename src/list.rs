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
use std::borrow::Borrow;

/// A persistent list with structural sharing.  This data structure supports fast get head,
/// get tail, and append.
///
/// # Complexity
///
/// Let *n* be the number of elements in the list.
///
/// ## Temporal complexity
///
/// | Operation         | Best case | Average | Worst case  |
/// |:----------------- | ---------:| -------:| -----------:|
/// | new               |      Θ(1) |    Θ(1) |        Θ(1) |
/// | cons              |      Θ(1) |    Θ(1) |        Θ(1) |
/// | tail              |      Θ(1) |    Θ(1) |        Θ(1) |
/// | clone             |      Θ(1) |    Θ(1) |        Θ(1) |
/// | iterator creation |      Θ(1) |    Θ(1) |        Θ(1) |
/// | iterator step     |      Θ(1) |    Θ(1) |        Θ(1) |
/// | iterator full     |      Θ(n) |    Θ(n) |        Θ(n) |
///
/// ## Space complexity
///
/// The space complexity is *Θ(n)*.
#[derive(Debug)]
pub struct List<T> {
    node: Arc<Node<T>>,
}

#[derive(Debug)]
enum Node<T> {
    Cons(T, Arc<Node<T>>),
    Nil,
}

impl<T> List<T> {
    pub fn new() -> List<T> {
        List {
            node: Arc::new(Node::Nil)
        }
    }

    pub fn head(&self) -> Option<&T> {
        match *self.node {
            Node::Cons(ref h, _) => Some(h),
            Node::Nil            => None,
        }
    }

    pub fn tail(&self) -> Option<List<T>> {
        match *self.node {
            Node::Cons(_, ref t) => Some(List { node: t.clone() }),
            Node::Nil            => None,
        }
    }

    pub fn cons(&self, v: T) -> List<T> {
        List {
            node: Arc::new(Node::Cons(v, self.node.clone()))
        }
    }

    pub fn iter(&self) -> Iter<T> {
        Iter::new(self)
    }
}

impl<T> Clone for List<T> {
    fn clone(&self) -> List<T> {
        List {
            node: self.node.clone()
        }
    }
}

impl<T> Display for List<T>
    where T: Display {
    fn fmt(&self, fmt: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        fmt.write_str("[")?;

        let mut first = true;

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

#[derive(Debug)]
pub struct Iter<'a, T: 'a> {
    next: &'a Node<T>
}

impl<'a, T> Iter<'a, T> {
    fn new(list: &List<T>) -> Iter<T> {
        Iter {
            next: list.node.borrow()
        }
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        match *self.next {
            Node::Cons(ref v, ref t) => {
                self.next = t;
                Some(v)
            },
            Node::Nil => None
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_new() -> () {
        let empty_list: List<i32> = List::new();

        match *empty_list.node {
            Node::Nil => (),
            _         => panic!("should be nil"),
        }
    }

    #[test]
    fn test_head() -> () {
        let empty_list: List<i32> = List::new();
        let singleton_list = List::new()
            .cons("hello");
        let list = List::new()
            .cons(3)
            .cons(2)
            .cons(1)
            .cons(0);

        assert_eq!(empty_list.head(), None);
        assert_eq!(singleton_list.head(), Some(&"hello"));
        assert_eq!(list.head(), Some(&0));
    }

    #[test]
    fn test_tail() -> () {
        let empty_list: List<i32> = List::new();
        let singleton_list = List::new()
            .cons("hello");
        let list = List::new()
            .cons(3)
            .cons(2)
            .cons(1)
            .cons(0);

        assert!(empty_list.tail().is_none());
        assert_eq!(singleton_list.tail().unwrap().head(), None);
        assert_eq!(list.tail().unwrap().head(), Some(&1));
    }

    #[test]
    fn test_display() -> () {
        let empty_list: List<i32> = List::new();
        let singleton_list = List::new()
            .cons("hello");
        let list = List::new()
            .cons(3)
            .cons(2)
            .cons(1)
            .cons(0);

        assert_eq!(format!("{}", empty_list), "[]");
        assert_eq!(format!("{}", singleton_list), "[hello]");
        assert_eq!(format!("{}", list), "[0, 1, 2, 3]");
    }

    #[test]
    fn test_iter() -> () {
        let limit = 1024;
        let mut list = List::new();
        let mut left = limit;

        for i in 0..limit {
            list = list.cons(i);
        }

        for v in list.iter() {
            left -= 1;
            assert_eq!(*v, left);
        }

        assert!(left == 0);
    }

    #[test]
    fn test_into_iterator() -> () {
        let list = List::new()
            .cons(3)
            .cons(2)
            .cons(1)
            .cons(0);
        let mut expected = 0;
        let mut left = 4;

        for n in &list {
            left -= 1;

            assert!(left >= 0);
            assert_eq!(*n, expected);

            expected += 1;
        }

        assert!(left == 0);
    }

    #[test]
    fn test_clone() -> () {
        let list = List::new()
            .cons("there")
            .cons("hello");
        let clone = list.clone();

        assert!(clone.iter().eq(list.iter()));
    }
}

/* TODO
 *
 * Implement traits:
 *
 *  - impl<T> Sync for List<T> where T: Sync
 *  - impl<T> Send for List<T> where T: Send
 *  - impl<T> IntoIterator for List<T>
 *  - impl<T> FromIterator<T>
 *  - impl<T> Ord for List<T> where T: Ord
 *  - impl<T> Eq for List<T> where T: Eq
 *  - impl<T> PartialEq<List<T>> for List<T> where T: PartialEq<T>
 *  - impl<T> PartialOrd<List<T>> for List<T> where T: PartialOrd<T>
 *  - impl<T> Hash for List<T> where T: Hash
 *  - impl<T> Default for List<T>
 *
 * Done:
 *  - impl<T> Clone for List<T> where T: Clone
 *  - impl<T> Debug for List<T> where T: Debug
 *  - impl<T> Display for List<T> where T: Display
 */
