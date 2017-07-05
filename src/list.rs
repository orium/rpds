use std::rc::Rc;
use std::fmt::Display;
use std::borrow::Borrow;

#[derive(Debug)]
pub struct List<T> {
    node: Rc<ListNode<T>>,
}

#[derive(Debug)]
enum ListNode<T> {
    Cons(T, Rc<ListNode<T>>),
    Nil,
}

impl<T> List<T> {
    pub fn new() -> List<T> {
        List {
            node: Rc::new(ListNode::Nil)
        }
    }

    pub fn head(&self) -> Option<&T> {
        match *self.node {
            ListNode::Cons(ref h, _) => Some(h),
            ListNode::Nil            => None,
        }
    }

    pub fn tail(&self) -> Option<List<T>> {
        match *self.node {
            ListNode::Cons(_, ref t) => Some(List { node: t.clone() }),
            ListNode::Nil            => None,
        }
    }

    pub fn cons(&self, v: T) -> List<T> {
        List {
            node: Rc::new(ListNode::Cons(v, self.node.clone()))
        }
    }

    pub fn iter(&self) -> Iter<T> {
        Iter {
            next: self.node.borrow()
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

pub struct Iter<'a, T: 'a> {
    next: &'a ListNode<T>
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        match *self.next {
            ListNode::Cons(ref v, ref t) => {
                self.next = t;
                Some(v)
            },
            ListNode::Nil => None
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn foo() -> () {
        let list: List<i32> = List::new()
            .cons(3)
            .cons(2)
            .cons(1)
            .cons(0);
        let tail = list.tail().unwrap();

        println!("{}", list);
        println!("{}", tail);
    }
}

/* TODO
 *
 * Use property based tests with https://github.com/BurntSushi/quickcheck
 *
 * Implement traits:
 *  - impl<T> Sync for List<T> where T: Sync
 *  - impl<T> Send for List<T> where T: Send
 *  - impl<T> IntoIterator for List<T>
 *  - impl<'a, T> IntoIterator for &'a List<T>
 *  - impl<T> FromIterator<T> for LinkedList<T>
 *  - impl<T> Ord for List<T> where T: Ord
 *  - impl<T> Eq for List<T> where T: Eq
 *  - impl<T> PartialEq<List<T>> for List<T> where T: PartialEq<T>
 *  - impl<T> Clone for List<T> where T: Clone
 *  - impl<T> PartialOrd<List<T>> for List<T> where T: PartialOrd<T>
 *  - impl<T> Hash for List<T> where T: Hash
 *  - impl<T> Default for List<T>
 *
 *  for the Vector we also want extend (see https://doc.rust-lang.org/std/collections/struct.LinkedList.html)
 *  + impl<T> Debug for List<T> where T: Debug
 *  + impl<T> Display for List<T> where T: Display
 */
