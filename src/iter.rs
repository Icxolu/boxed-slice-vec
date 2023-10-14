use crate::FixedVec;
use std::{fmt, iter::FusedIterator, mem, ptr, slice};

impl<'a, T> IntoIterator for &'a FixedVec<T> {
    type Item = &'a T;
    type IntoIter = slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.as_slice().iter()
    }
}

impl<'a, T> IntoIterator for &'a mut FixedVec<T> {
    type Item = &'a mut T;
    type IntoIter = slice::IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.as_mut_slice().iter_mut()
    }
}

impl<T> IntoIterator for FixedVec<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter { idx: 0, v: self }
    }
}

pub struct IntoIter<T> {
    idx: usize,
    v: FixedVec<T>,
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.idx == self.v.len() {
            None
        } else {
            unsafe {
                let index = self.idx;
                self.idx = index + 1;
                Some(ptr::read(self.v.get_unchecked_ptr(index)))
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.v.len() - self.idx;
        (len, Some(len))
    }
}

impl<T> DoubleEndedIterator for IntoIter<T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.idx == self.v.len() {
            None
        } else {
            unsafe {
                let new_len = self.v.len() - 1;
                self.v.set_len(new_len);
                Some(ptr::read(self.v.get_unchecked_ptr(new_len)))
            }
        }
    }
}

impl<T> ExactSizeIterator for IntoIter<T> {}
impl<T> FusedIterator for IntoIter<T> {}

impl<T> Drop for IntoIter<T> {
    fn drop(&mut self) {
        // panic safety: Set length to 0 before dropping elements.
        let idx = self.idx;
        let len = self.v.len();
        // drop the remaining elements
        unsafe {
            self.v.set_len(0);
            let elements = &mut self.v.slice[idx..len] as *mut [mem::MaybeUninit<T>] as *mut [T];
            ptr::drop_in_place(elements);
        }
    }
}

impl<T> Clone for IntoIter<T>
where
    T: Clone,
{
    fn clone(&self) -> IntoIter<T> {
        let mut v = FixedVec::with_capacity(self.v.len() - self.idx);
        v.extend(self.v[self.idx..].iter().cloned());
        v.into_iter()
    }
}

impl<T> fmt::Debug for IntoIter<T>
where
    T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_list().entries(&self.v[self.idx..]).finish()
    }
}
