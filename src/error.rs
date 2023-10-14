use std::fmt;

/// Error value indicating insufficient capacity
pub struct CapacityError<T>(pub T);

impl<T> fmt::Debug for CapacityError<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "CapacityError: insufficient capacity")
    }
}

impl<T> fmt::Display for CapacityError<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "insufficient capacity")
    }
}

impl<T: Clone> Clone for CapacityError<T> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<T> std::error::Error for CapacityError<T> {}
