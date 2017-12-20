/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

pub trait VecUtils {
    type Item;

    fn cloned_set(&self, index: usize, value: Self::Item) -> Self;
    fn cloned_insert(&self, index: usize, value: Self::Item) -> Self;
    fn cloned_remove(&self, index: usize) -> Self;
    fn cloned_remove_last(&self) -> Self;
}

impl<T: Clone> VecUtils for Vec<T> {
    type Item = T;

    fn cloned_set(&self, index: usize, value: T) -> Vec<T> {
        let capacity = self.len() + if index == self.len() { 1 } else { 0 };
        let mut cloned_vec = Vec::with_capacity(capacity);

        debug_assert!(index <= self.len());

        cloned_vec.extend_from_slice(&self[0..index]);
        cloned_vec.push(value);
        if index < self.len() {
            cloned_vec.extend_from_slice(&self[(index + 1)..self.len()]);
        }

        cloned_vec
    }

    fn cloned_insert(&self, index: usize, value: T) -> Vec<T> {
        let mut cloned_vec = Vec::with_capacity(self.len() + 1);

        debug_assert!(index <= self.len());

        cloned_vec.extend_from_slice(&self[0..index]);
        cloned_vec.push(value);
        cloned_vec.extend_from_slice(&self[index..self.len()]);

        cloned_vec
    }

    fn cloned_remove(&self, index: usize) -> Vec<T> {
        let mut cloned_vec = Vec::with_capacity(self.len() - 1);

        debug_assert!(index < self.len());

        cloned_vec.extend_from_slice(&self[0..index]);
        cloned_vec.extend_from_slice(&self[(index + 1)..self.len()]);

        cloned_vec
    }

    fn cloned_remove_last(&self) -> Vec<T> {
        debug_assert!(self.len() > 0);
        self.cloned_remove(self.len() - 1)
    }
}

#[cfg(test)]
mod test;
