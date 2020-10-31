/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use alloc::vec::Vec;
use core::mem::size_of_val;
use core::slice;

/// Sparse array of size `8⋅size_of::<usize>()`.  The space used is proportional to the number of
/// elements set.
#[derive(Debug, PartialEq, Eq)]
pub struct SparseArrayUsize<T> {
    bitmap: usize,
    array: Vec<T>,
}

mod sparse_array_usize_utils {
    #[inline]
    pub fn map_index(bitmap: usize, virtual_index: usize) -> Option<usize> {
        if bitmap & (1_usize << virtual_index) == 0 {
            None
        } else {
            let mask = (1_usize << virtual_index) - 1;

            Some((bitmap & mask).count_ones() as usize)
        }
    }
}

impl<T> SparseArrayUsize<T> {
    pub fn new() -> SparseArrayUsize<T> {
        SparseArrayUsize { bitmap: 0, array: Vec::new() }
    }

    #[inline]
    pub fn get(&self, index: usize) -> Option<&T> {
        debug_assert!(index < 8 * size_of_val(&self.bitmap));

        sparse_array_usize_utils::map_index(self.bitmap, index).map(|i| &self.array[i])
    }

    #[inline]
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        debug_assert!(index < 8 * size_of_val(&self.bitmap));

        sparse_array_usize_utils::map_index(self.bitmap, index).map(move |i| &mut self.array[i])
    }

    #[inline]
    pub fn first(&self) -> Option<&T> {
        self.array.first()
    }

    #[inline]
    pub fn pop(&mut self) -> Option<T> {
        self.array.pop()
    }

    pub fn set(&mut self, index: usize, value: T) {
        debug_assert!(index < 8 * size_of_val(&self.bitmap));

        match sparse_array_usize_utils::map_index(self.bitmap, index) {
            Some(i) => self.array[i] = value,
            None => {
                let new_bitmap = self.bitmap | (1 << index);
                let i = sparse_array_usize_utils::map_index(new_bitmap, index).unwrap();

                self.bitmap = new_bitmap;
                self.array.insert(i, value);
            }
        }
    }

    pub fn remove(&mut self, index: usize) {
        if let Some(i) = sparse_array_usize_utils::map_index(self.bitmap, index) {
            self.bitmap ^= 1 << index;
            self.array.remove(i);
        }
    }

    #[inline]
    pub fn size(&self) -> usize {
        self.bitmap.count_ones() as usize
    }

    pub fn iter(&self) -> slice::Iter<'_, T> {
        self.array.iter()
    }
}

impl<T: Clone> Clone for SparseArrayUsize<T> {
    fn clone(&self) -> SparseArrayUsize<T> {
        SparseArrayUsize { bitmap: self.bitmap, array: Vec::clone(&self.array) }
    }
}

#[cfg(test)]
mod test;
