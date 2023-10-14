#![deny(missing_docs)]
//! A contiguous array type with heap-allocated contents, written
//! [`FixedVec<T>`]
//!
//! Vectors have O(1) indexing, O(1) push (to the end) and O(1) pop (from the
//! end).
//!
//! # Examples
//!
//! You can create a [`FixedVec`] with [`FixedVec::with_capacity`]:
//!
//! ```
//! # use boxed_slice_vec::FixedVec;
//! let v: FixedVec<i32> = FixedVec::with_capacity(10);
//! ```
//!
//! You can [`push`] values onto the end of a vector:
//!
//! ```
//! # use boxed_slice_vec::FixedVec;
//! let mut v = FixedVec::with_capacity(10);
//!
//! v.push(3);
//! ```
//!
//! Popping values works in much the same way:
//!
//! ```
//! # use boxed_slice_vec::FixedVec;
//! let mut v = FixedVec::from([1, 2]);
//!
//! let two = v.pop();
//! ```
//!
//! Vectors also support indexing (through the [`Index`] and [`IndexMut`]
//! traits):
//!
//! ```
//! # use boxed_slice_vec::FixedVec;
//! let mut v = FixedVec::from([1, 2, 3]);
//! let three = v[2];
//! v[1] = v[1] + 5;
//! ```
//!
//! [`push`]: FixedVec::push
//! [`Index`]: std::ops::Index
//! [`IndexMut`]: std::ops::IndexMut
//!
//! # Comparison
//!
//! There are several other Vec-like crates which should be considered as
//! possible alternatives to [FixedVec].
//!
//! - The standard library’s [Vec] has a runtime dynamic capacity backed by an
//!   allocator. The capacity of the vecor is allocated at runtime and is
//!   allowed to grow.
//! - [arrayvec](https://crates.io/crates/arrayvec) has a compile-time fixed
//!   capacity.
//! - [tinyvec](https://crates.io/crates/tinyvec) has several variants for
//!   compile-time fixed capacity, backed by borrowed slice and growable inline
//!   storage vectors.
//! - [smallvec](https://crates.io/crates/smallvec) growable vector which can
//!   store a small number of elements inline.
//! - [FixedVec] (this crate) implements a runtime fixed capacity vector backed by a boxed
//!   slice.
mod error;
mod extend;
mod iter;

use std::fmt;
use std::mem;
use std::ops;
use std::ptr;

pub use crate::error::CapacityError;

/// A vector with a fixed capacity.
///
/// The [`FixedVec`] is a vector backed by a boxed slice (`Box<[T]>`). Its
/// capacity is allocated at runtime using [`with_capacity()`]. In contrast to
/// the standard library's [`Vec<T>`] this vector is *not* growable. It
/// allocates a fixed capacity upfront and stays that way until it is dropped.
///
/// [`with_capacity()`]: Self::with_capacity
pub struct FixedVec<T> {
    slice: Box<[mem::MaybeUninit<T>]>,
    len: usize,
}

impl<T> FixedVec<T> {
    /// Create a new [`FixedVec`] with the given capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// # use boxed_slice_vec::*;
    /// let mut array = FixedVec::with_capacity(16);
    /// array.push(1);
    /// array.push(2);
    /// assert_eq!(&array[..], &[1, 2]);
    /// assert_eq!(array.capacity(), 16);
    /// ```
    pub fn with_capacity(cap: usize) -> Self {
        let slice = if cap == 0 || mem::size_of::<T>() == 0 {
            ptr::slice_from_raw_parts_mut(ptr::NonNull::dangling().as_ptr(), cap)
        } else {
            let layout = std::alloc::Layout::array::<T>(cap).expect("layout overflow");
            // SAFETY: `T` is not a ZST, and `cap` is not 0
            let ptr = unsafe { std::alloc::alloc(layout) as *mut mem::MaybeUninit<T> };
            if ptr.is_null() {
                std::alloc::handle_alloc_error(layout);
            }
            ptr::slice_from_raw_parts_mut(ptr, cap)
        };

        Self {
            // SAFETY: "It is valid to convert both ways between a Box and a raw
            // pointer allocated with the Global allocator, given that the Layout
            // used with the allocator is correct for the type."
            // https://doc.rust-lang.org/stable/std/boxed/index.html#memory-layout
            slice: unsafe { Box::from_raw(slice) },
            len: 0,
        }
    }

    /// Returns the capacity of the [`FixedVec`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use boxed_slice_vec::*;
    ///
    /// let array = FixedVec::from([1, 2, 3]);
    /// assert_eq!(array.capacity(), 3);
    /// ```
    #[inline]
    pub fn capacity(&self) -> usize {
        self.slice.len()
    }

    /// Returns the number of elements in the vector, also referred to as its
    /// 'length'.
    ///
    /// # Examples
    ///
    /// ```
    /// # use boxed_slice_vec::*;
    /// let mut array = FixedVec::from([1, 2, 3]);
    /// array.pop();
    /// assert_eq!(array.len(), 2);
    /// ```
    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Forces the length of the vector to `new_len`.
    ///
    /// This is a low-level operation that maintains none of the normal
    /// invariants of the type. Normally changing the length of a vector is done
    /// using one of the safe operations instead, [`truncate`], [`extend`], or
    /// [`clear`].
    ///
    /// [`truncate`]: Self::truncate
    /// [`extend`]: Self::extend
    /// [`clear`]: Self::clear
    ///
    /// # Safety
    /// - `new_len` must be less than or equal to [`capacity()`].
    /// - The elements at `old_len..new_len` must be initialized.
    ///
    /// [`capacity()`]: Vec::capacity
    #[inline]
    pub unsafe fn set_len(&mut self, new_len: usize) {
        debug_assert!(new_len <= self.capacity());
        self.len = new_len;
    }

    /// Returns the capacity left in the [`FixedVec`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use boxed_slice_vec::*;
    /// let mut array = FixedVec::from([1, 2, 3]);
    /// array.pop();
    /// assert_eq!(array.remaining_capacity(), 1);
    /// ```
    #[inline]
    pub fn remaining_capacity(&self) -> usize {
        self.capacity() - self.len()
    }

    /// Returns whether the [`FixedVec`] is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// # use boxed_slice_vec::FixedVec;
    /// let mut array = FixedVec::from([1]);
    /// array.pop();
    /// assert_eq!(array.is_empty(), true);
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns whether the [`FixedVec`] is completely filled to its capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// # use boxed_slice_vec::FixedVec;
    /// let mut array = FixedVec::with_capacity(1);
    /// assert!(!array.is_full());
    /// array.push(1);
    /// assert!(array.is_full());
    /// ```
    #[inline]
    pub fn is_full(&self) -> bool {
        self.len() == self.capacity()
    }

    /// Push `element` to the end of the vector.
    ///
    /// ***Panics*** if the vector is already full. See [`try_push()`] for a
    /// fallible version.
    ///
    /// [`try_push()`]: Self::try_push
    ///
    /// # Examples
    ///
    /// ```
    /// # use boxed_slice_vec::FixedVec;
    /// let mut array = FixedVec::with_capacity(2);
    ///
    /// array.push(1);
    /// array.push(2);
    ///
    /// assert_eq!(&array[..], &[1, 2]);
    /// ```
    #[track_caller]
    #[inline]
    pub fn push(&mut self, element: T) {
        self.try_push(element).expect("enough capacity")
    }

    /// Push `element` to the end of the vector.
    ///
    /// Returns `Ok` if the push succeeds, or `Err` containing `element` if the
    /// vector is already full.
    ///
    /// # Examples
    ///
    /// ```
    /// # use boxed_slice_vec::FixedVec;
    /// let mut array = FixedVec::with_capacity(2);
    ///
    /// let push1 = array.try_push(1);
    /// let push2 = array.try_push(2);
    ///
    /// assert!(push1.is_ok());
    /// assert!(push2.is_ok());
    ///
    /// assert_eq!(&array[..], &[1, 2]);
    ///
    /// let overflow = array.try_push(3);
    ///
    /// assert!(overflow.is_err());
    /// ```
    pub fn try_push(&mut self, element: T) -> Result<(), CapacityError<T>> {
        if self.len == self.slice.len() {
            Err(CapacityError(element))
        } else {
            self.slice[self.len].write(element);
            // SAFETY: we initialized the next element above, so we can increase
            // the length by 1
            unsafe { self.set_len(self.len + 1) };
            Ok(())
        }
    }

    /// Remove the last element in the vector and return it.
    ///
    /// Returns `Some` containing the element if the vector is non-empty,
    /// otherwise `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use boxed_slice_vec::FixedVec;
    /// let mut array = FixedVec::with_capacity(2);
    ///
    /// array.push(1);
    ///
    /// assert_eq!(array.pop(), Some(1));
    /// assert_eq!(array.pop(), None);
    /// ```
    pub fn pop(&mut self) -> Option<T> {
        let len = self.len();
        if len == 0 {
            None
        } else {
            // SAFETY: All elements upto and including `len - 1` are properly
            // initialized, so we decrease the length of the vector and return
            // the last element.
            unsafe {
                self.set_len(len - 1);
                Some(self.slice[len - 1].assume_init_read())
            }
        }
    }

    /// Insert `element` at position `idx`.
    ///
    /// This shifts all elements after `idx` up by one.
    ///
    /// ***Panics*** if the array is full or the `index` is out of bounds. See
    /// [`try_insert()`] for fallible version.
    ///
    /// [`try_insert()`]: Self::try_insert
    ///
    /// # Examples
    ///
    /// ```
    /// # use boxed_slice_vec::FixedVec;
    /// let mut array = FixedVec::with_capacity(2);
    ///
    /// array.insert(0, "x");
    /// array.insert(0, "y");
    /// assert_eq!(&array[..], &["y", "x"]);
    /// ```
    #[track_caller]
    #[inline]
    pub fn insert(&mut self, idx: usize, element: T) {
        self.try_insert(idx, element).expect("enough capacity")
    }

    /// Insert `element` at position `idx`.
    ///
    /// This shifts all elements after `idx` up by one. If the vector is already
    /// at full capacity an error containing the given `element` is returned.
    ///
    /// ***Panics*** if `idx` is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// # use boxed_slice_vec::FixedVec;
    /// let mut array = FixedVec::with_capacity(2);
    ///
    /// assert!(array.try_insert(0, "x").is_ok());
    /// assert!(array.try_insert(0, "y").is_ok());
    /// assert!(array.try_insert(0, "z").is_err());
    /// assert_eq!(&array[..], &["y", "x"]);
    /// ```
    #[track_caller]
    pub fn try_insert(&mut self, idx: usize, element: T) -> Result<(), CapacityError<T>> {
        let len = self.len();
        if idx > len {
            panic!(
                "FixedVec::try_insert: index {} is out of bounds in vector of length {}",
                idx, len
            )
        }
        if len == self.capacity() {
            Err(CapacityError(element))
        } else {
            // follows is just like Vec<T>
            // infallible
            // The spot to put the new value
            {
                // SAFETY: `idx` is in bounds
                let p = unsafe { self.get_unchecked_ptr(idx) };
                // Make space by shifting all elements from index by 1 to the right
                // SAFETY: both `src` and `dst` are valid and properly aligned
                unsafe { ptr::copy(p, p.offset(1), len - idx) }
                // initialize the now free slot
                self.slice[idx].write(element);
            }
            // SAFETY: we inserted and initialiued 1 new element
            unsafe { self.set_len(len + 1) }
            Ok(())
        }
    }

    /// Fill the vector until its capacity has been reached.
    ///
    /// Successively fills unused space in the spare capacity of the vector with
    /// elements from the iterator. It then returns the remaining iterator
    /// without exhausting it. This also allows appending the head of an
    /// infinite iterator.
    ///
    /// This is an alternative to `Extend::extend` method for cases where the
    /// length of the iterator can not be checked. Since this vector can not
    /// reallocate to increase its capacity, it is unclear what to do with
    /// remaining elements in the iterator and the iterator itself. The
    /// interface also provides no way to communicate this to the caller.
    ///
    /// ## Examples
    ///
    /// ```
    /// # use boxed_slice_vec::*;
    /// let mut sv = FixedVec::with_capacity(4);
    /// let mut to_inf = sv.fill(0..);
    /// assert_eq!(&sv[..], [0, 1, 2, 3]);
    /// assert_eq!(to_inf.next(), Some(4));
    /// ```
    #[track_caller]
    pub fn fill<I: IntoIterator<Item = T>>(&mut self, iter: I) -> I::IntoIter {
        let mut iter = iter.into_iter();
        for element in iter.by_ref().take(self.capacity() - self.len()) {
            self.push(element);
        }
        iter
    }

    /// Removes the element at `idx` by shifting down all following elements.
    ///
    /// ***Panics*** if `idx` is out of bounds. See [`try_remove()`] for a
    /// fallible version.
    ///
    /// [`try_remove()`]: Self::try_remove
    ///
    /// # Examples
    ///
    /// ```
    /// # use boxed_slice_vec::FixedVec;
    /// let mut array = FixedVec::from([1, 2, 3]);
    ///
    /// let removed_elt = array.remove(0);
    /// assert_eq!(removed_elt, 1);
    /// assert_eq!(&array[..], &[2, 3]);
    /// ```
    #[track_caller]
    #[inline]
    pub fn remove(&mut self, idx: usize) -> T {
        self.try_remove(idx).unwrap_or_else(|| {
            panic!(
                "FixedVec::remove: index {} is out of bounds in vector of length {}",
                idx,
                self.len()
            )
        })
    }

    /// Removes the element at `idx` by shifting down all following elements.
    ///
    /// Returns `Some` if `idx` is in bounds otherwise `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use boxed_slice_vec::FixedVec;
    /// let mut array = FixedVec::from([1, 2, 3]);
    ///
    /// assert!(array.try_remove(0).is_some());
    /// assert_eq!(&array[..], &[2, 3]);
    ///
    /// assert!(array.try_remove(2).is_none());
    /// assert!(array.try_remove(10).is_none());
    /// ```
    pub fn try_remove(&mut self, idx: usize) -> Option<T> {
        let len = self.len();
        if idx >= len {
            None
        } else {
            let el;
            // follows is just like Vec<T>
            // infallible
            {
                // copy element out, unsafely having a copy of the value on
                // the stack and in the vector at the same time.
                el = unsafe { self.slice[idx].assume_init_read() };
                let p = unsafe { self.get_unchecked_ptr(idx) };
                // Shift everything down to fill in that spot.
                unsafe { ptr::copy(p.offset(1), p, len - idx - 1) }
            }
            unsafe { self.set_len(len - 1) }
            Some(el)
        }
    }

    /// Removes the element at `idx` by swapping the last element into its
    /// place.
    ///
    /// This operation is O(1).
    ///
    /// ***Panics*** if `idx` is out of bounds. See [`try_swap_remove()`] for a
    /// fallible version.
    ///
    /// [`try_swap_remove()`]: Self::try_swap_remove
    ///
    /// # Examples
    ///
    /// ```
    /// # use boxed_slice_vec::FixedVec;
    /// let mut array = FixedVec::from([1, 2, 3]);
    ///
    /// assert_eq!(array.swap_remove(0), 1);
    /// assert_eq!(&array[..], &[3, 2]);
    ///
    /// assert_eq!(array.swap_remove(1), 2);
    /// assert_eq!(&array[..], &[3]);
    /// ```
    #[track_caller]
    #[inline]
    pub fn swap_remove(&mut self, idx: usize) -> T {
        self.try_swap_remove(idx).unwrap_or_else(|| {
            panic!(
                "FixedVec::swap_remove: index {} is out of bounds in vector of length {}",
                idx,
                self.len()
            )
        })
    }

    /// Removes the element at `idx` by swapping the last element into its
    /// place.
    ///
    /// This operation is O(1).
    ///
    /// Returns `Some` containing the element if the index is in bounds, else
    /// `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use boxed_slice_vec::FixedVec;
    /// let mut array = FixedVec::from([1, 2, 3]);
    ///
    /// assert_eq!(array.try_swap_remove(0), Some(1));
    /// assert_eq!(&array[..], &[3, 2]);
    ///
    /// assert_eq!(array.try_swap_remove(10), None);
    /// ```
    pub fn try_swap_remove(&mut self, idx: usize) -> Option<T> {
        let len = self.len();
        if idx >= len {
            return None;
        }
        self.swap(idx, len - 1);
        self.pop()
    }

    /// Copy all elements from the slice and append to the end of the vector.
    ///
    /// ***Panics*** if the [`remaining_capacity()`] is smaller then the length
    /// of the provided slice. See [`try_extend_from_slice()`] for a fallible
    /// version.
    ///
    /// [`remaining_capacity()`]: Self::remaining_capacity
    /// [`try_extend_from_slice()`]: Self::try_extend_from_slice
    #[track_caller]
    #[inline]
    pub fn extend_from_slice(&mut self, other: &[T])
    where
        T: Copy,
    {
        self.try_extend_from_slice(other).expect("enough capacity")
    }

    /// Copy all elements from the slice and append to the end of the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// # use boxed_slice_vec::FixedVec;
    /// let mut vec = FixedVec::<usize>::with_capacity(10);
    /// vec.push(1);
    /// vec.try_extend_from_slice(&[2, 3]).unwrap();
    /// assert_eq!(&vec[..], &[1, 2, 3]);
    /// ```
    ///
    /// # Errors
    ///
    /// Returns an error if the [`remaining_capacity()`] is smaller then the
    /// length of the provided slice.
    ///
    /// [`remaining_capacity()`]: Self::remaining_capacity
    pub fn try_extend_from_slice(&mut self, other: &[T]) -> Result<(), CapacityError<()>>
    where
        T: Copy,
    {
        if self.remaining_capacity() < other.len() {
            return Err(CapacityError(()));
        }

        let self_len = self.len();
        let other_len = other.len();

        unsafe {
            let dst = self.get_unchecked_ptr(self_len);
            ptr::copy_nonoverlapping(other.as_ptr(), dst, other_len);
            self.set_len(self_len + other_len);
        }
        Ok(())
    }

    /// Shortens the vector, keeping the first `new_len` elements and dropping
    /// the rest.
    ///
    /// If `new_len` is greater than the vector’s current length, this has no
    /// effect.
    ///
    /// Note that this method has no effect on the allocated capacity of the
    /// vector.
    ///
    /// # Examples
    ///
    /// ```
    /// # use boxed_slice_vec::FixedVec;
    /// let mut array = FixedVec::from([1, 2, 3, 4, 5]);
    /// array.truncate(3);
    /// assert_eq!(&array[..], &[1, 2, 3]);
    /// array.truncate(4);
    /// assert_eq!(&array[..], &[1, 2, 3]);
    /// ```
    pub fn truncate(&mut self, new_len: usize) {
        let len = self.len();
        if new_len >= len {
            return;
        }
        unsafe { self.set_len(new_len) };
        let tail = &mut self.slice[new_len..len] as *mut [mem::MaybeUninit<T>] as *mut [T];
        // slices have drop glue that drops each element sequentially
        unsafe { ptr::drop_in_place(tail) };
    }

    /// Removes all elements in the vector.
    ///
    /// Note that this method has no effect on the allocated capacity of the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// # use boxed_slice_vec::FixedVec;
    /// let mut v = FixedVec::from([1, 2, 3]);
    /// v.clear();
    /// assert!(v.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.truncate(0);
    }

    /// Returns a slice containing all elements of the vector.
    ///
    /// # Examples
    /// ```
    /// # use boxed_slice_vec::FixedVec;
    /// use std::io::{self, Write};
    /// let buffer = FixedVec::from([1, 2, 3, 5, 8]);
    /// io::sink().write(buffer.as_slice()).unwrap();
    /// ```
    pub fn as_slice(&self) -> &[T] {
        // SAFETY: all elements upto `self.len` have been initialized
        unsafe { &*(&self.slice[..self.len] as *const [mem::MaybeUninit<T>] as *const [T]) }
    }

    /// Returns a mutable slice containing all elements of the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// # use boxed_slice_vec::FixedVec;
    /// use std::io::{self, Read};
    /// let mut buffer = FixedVec::from([0; 3]);
    /// io::repeat(0b101).read_exact(buffer.as_mut_slice()).unwrap();
    /// ```
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        // SAFETY: all elements upto `self.len` have been initialized
        unsafe { &mut *(&mut self.slice[..self.len] as *mut [mem::MaybeUninit<T>] as *mut [T]) }
    }

    /// Returns a raw pointer to the vector's backing memory.
    pub fn as_ptr(&self) -> *const T {
        self.slice.as_ptr() as _
    }

    /// Returns a raw mutable pointer to the vector's backing memory.
    pub fn as_mut_ptr(&mut self) -> *mut T {
        self.slice.as_mut_ptr() as _
    }

    unsafe fn get_unchecked_ptr(&mut self, idx: usize) -> *mut T {
        self.slice.as_mut_ptr().add(idx).cast()
    }
}

impl<T> Drop for FixedVec<T> {
    fn drop(&mut self) {
        self.clear()
    }
}

impl<T> ops::Deref for FixedVec<T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl<T> ops::DerefMut for FixedVec<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_mut_slice()
    }
}

impl<T> Clone for FixedVec<T>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        let mut vec = FixedVec::with_capacity(self.capacity());
        vec.extend(self.iter().cloned());
        vec
    }
}

impl<T> PartialEq for FixedVec<T>
where
    T: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl<T> PartialEq<[T]> for FixedVec<T>
where
    T: PartialEq,
{
    fn eq(&self, other: &[T]) -> bool {
        self.as_slice() == other
    }
}

impl<T> Eq for FixedVec<T> where T: Eq {}

impl<T> AsRef<[T]> for FixedVec<T> {
    fn as_ref(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T> AsMut<[T]> for FixedVec<T> {
    fn as_mut(&mut self) -> &mut [T] {
        self.as_mut_slice()
    }
}

impl<T> fmt::Debug for FixedVec<T>
where
    T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.as_slice().fmt(f)
    }
}

impl<T, const N: usize> From<[T; N]> for FixedVec<T> {
    fn from(array: [T; N]) -> Self {
        let array = mem::ManuallyDrop::new(array);
        let mut vec = FixedVec::with_capacity(N);
        unsafe {
            ptr::copy_nonoverlapping(array.as_ptr(), vec.get_unchecked_ptr(vec.len()), N);
            vec.set_len(N);
        }
        vec
    }
}

impl<T> From<&[T]> for FixedVec<T>
where
    T: Copy,
{
    fn from(slice: &[T]) -> Self {
        let mut vec = FixedVec::with_capacity(slice.len());
        vec.extend_from_slice(slice);
        vec
    }
}

impl<T> From<Box<[T]>> for FixedVec<T>
where
    T: Copy,
{
    fn from(slice: Box<[T]>) -> Self {
        Self {
            len: slice.len(),
            // SAFETY: `MaybeUninit` is repr(transparent) so we can freely
            // interpret an array of initialized values as an array of
            // potentially uninitialized values
            slice: unsafe { mem::transmute(slice) },
        }
    }
}

impl<T> From<Vec<T>> for FixedVec<T>
where
    T: Copy,
{
    fn from(vec: Vec<T>) -> Self {
        vec.into_boxed_slice().into()
    }
}
