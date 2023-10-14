use crate::FixedVec;
use std::{mem, ptr};

struct ScopeExitGuard<T, Data, F>
where
    F: FnMut(&Data, &mut T),
{
    value: T,
    data: Data,
    f: F,
}

impl<T, Data, F> Drop for ScopeExitGuard<T, Data, F>
where
    F: FnMut(&Data, &mut T),
{
    fn drop(&mut self) {
        (self.f)(&self.data, &mut self.value)
    }
}

/// Rawptr add but uses arithmetic distance for ZST
unsafe fn raw_ptr_add<T>(ptr: *mut T, offset: usize) -> *mut T {
    if mem::size_of::<T>() == 0 {
        // Special case for ZST
        ptr.cast::<u8>().wrapping_add(offset).cast()
    } else {
        ptr.add(offset)
    }
}

impl<T> Extend<T> for FixedVec<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        let take = self.capacity() - self.len();
        let len = self.len();
        let mut ptr = unsafe { raw_ptr_add(self.as_mut_ptr(), len) };
        let end_ptr = unsafe { raw_ptr_add(ptr, take) };
        // Keep the length in a separate variable, write it back on scope
        // exit. To help the compiler with alias analysis and stuff.
        // We update the length to handle panic in the iteration of the
        // user's iterator, without dropping any elements on the floor.
        let mut guard = ScopeExitGuard {
            value: &mut self.len,
            data: len,
            f: move |&len, self_len: &mut &mut usize| {
                **self_len = len;
            },
        };
        let mut iter = iter.into_iter();
        loop {
            if let Some(elt) = iter.next() {
                if ptr == end_ptr {
                    panic!("ArrayVec: capacity exceeded in extend");
                }
                debug_assert_ne!(ptr, end_ptr);
                unsafe {
                    if mem::size_of::<T>() == 0 {
                        ptr::write(ptr::NonNull::dangling().as_mut(), elt);
                    } else {
                        ptr.write(elt);
                    }
                }
                ptr = unsafe { raw_ptr_add(ptr, 1) };
                guard.data += 1;
            } else {
                return; // success
            }
        }
    }
}
