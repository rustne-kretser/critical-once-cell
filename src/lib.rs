// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Drop-in replacements for [`core::lazy::OnceCell`] and
//! [`core::lazy::Lazy`], backed by [`critical_section`].
//!
//! ## Examples
//! ### `CriticalOnceCell`
//!
//! ```
//! use critical_once_cell::CriticalOnceCell;
//!
//! static CELL: CriticalOnceCell<String> = CriticalOnceCell::new();
//!
//! fn main() {
//!     CELL.set("Hello, World!".to_owned()).unwrap();
//!
//!     assert_eq!(*CELL.get().unwrap(), "Hello, World!");
//! }
//! ```
//!
//! ### `CriticalLazy`
//!
//! ```
//! use critical_once_cell::CriticalLazy;
//!
//! static LAZY: CriticalLazy<String> = CriticalLazy::new(|| "Hello, World!".to_owned());
//!
//! fn main() {
//!     assert_eq!(*LAZY, "Hello, World!");
//! }
//! ```

#![no_std]

use core::{
    cell::{Cell, UnsafeCell},
    convert::Infallible,
    ops::Deref,
};

/// A thread-safe cell which can be written to only once.
///
/// # Examples
///
/// ```
/// use critical_once_cell::CriticalOnceCell;
///
/// let cell = CriticalOnceCell::new();
/// assert!(cell.get().is_none());
///
/// let value: &String = cell.get_or_init(|| {
///     "Hello, World!".to_string()
/// });
/// assert_eq!(value, "Hello, World!");
/// assert!(cell.get().is_some());
/// ```
pub struct CriticalOnceCell<T> {
    inner: UnsafeCell<Option<T>>,
}

impl<T> CriticalOnceCell<T> {
    /// Creates a new empty cell.
    pub const fn new() -> Self {
        Self {
            inner: UnsafeCell::new(None),
        }
    }

    /// Gets the reference to the underlying value.
    ///
    /// Returns `None` if the cell is empty.
    pub fn get(&self) -> Option<&T> {
        critical_section::with(|_| {
            let cell = unsafe { &mut *self.inner.get() };

            cell.as_ref()
        })
    }

    /// Gets the mutable reference to the underlying value.
    ///
    /// Returns `None` if the cell is empty.
    pub fn get_mut(&mut self) -> Option<&mut T> {
        critical_section::with(|_| {
            let cell = unsafe { &mut *self.inner.get() };

            cell.as_mut()
        })
    }

    /// Sets the contents of the cell to `value`.
    ///
    /// # Errors
    ///
    /// This method returns `Ok(())` if the cell was empty and `Err(value)` if
    /// it was full.
    ///
    /// # Examples
    ///
    /// ```
    /// use critical_once_cell::CriticalOnceCell;
    ///
    /// let cell = CriticalOnceCell::new();
    /// assert!(cell.get().is_none());
    ///
    /// assert_eq!(cell.set(92), Ok(()));
    /// assert_eq!(cell.set(62), Err(62));
    ///
    /// assert!(cell.get().is_some());
    /// ```
    pub fn set(&self, value: T) -> Result<(), T> {
        critical_section::with(|_| {
            let cell = unsafe { &mut *self.inner.get() };

            if cell.is_none() {
                *cell = Some(value);
                Ok(())
            } else {
                Err(value)
            }
        })
    }

    /// Gets the contents of the cell, initializing it with `f`
    /// if the cell was empty.
    ///
    /// # Panics
    ///
    /// If `f` panics, the panic is propagated to the caller, and the cell
    /// remains uninitialized.
    ///
    /// It is an error to reentrantly initialize the cell from `f`. Doing
    /// so results in a panic.
    ///
    /// # Examples
    ///
    /// ```
    /// use critical_once_cell::CriticalOnceCell;
    ///
    /// let cell = CriticalOnceCell::new();
    /// let value = cell.get_or_init(|| 92);
    /// assert_eq!(value, &92);
    /// let value = cell.get_or_init(|| unreachable!());
    /// assert_eq!(value, &92);
    /// ```
    pub fn get_or_init<F>(&self, f: F) -> &T
    where
        F: FnOnce() -> T,
    {
        unsafe {
            self.get_or_try_init::<_, Infallible>(|| Ok(f()))
                .unwrap_unchecked()
        }
    }

    /// Gets the contents of the cell, initializing it with `f` if
    /// the cell was empty. If the cell was empty and `f` failed, an
    /// error is returned.
    ///
    /// # Panics
    ///
    /// If `f` panics, the panic is propagated to the caller, and the cell
    /// remains uninitialized.
    ///
    /// It is an error to reentrantly initialize the cell from `f`. Doing
    /// so results in a panic.
    ///
    /// # Examples
    ///
    /// ```
    /// use critical_once_cell::CriticalOnceCell;
    ///
    /// let cell = CriticalOnceCell::new();
    /// assert_eq!(cell.get_or_try_init(|| Err(())), Err(()));
    /// assert!(cell.get().is_none());
    /// let value = cell.get_or_try_init(|| -> Result<i32, ()> {
    ///     Ok(92)
    /// });
    /// assert_eq!(value, Ok(&92));
    /// assert_eq!(cell.get(), Some(&92))
    /// ```
    pub fn get_or_try_init<F, E>(&self, f: F) -> Result<&T, E>
    where
        F: FnOnce() -> Result<T, E>,
    {
        critical_section::with(|_| {
            let cell = {
                // Get shared reference first, to avoid retagging in case
                // there are other references in use
                let cell = unsafe { &*self.inner.get() };

                if cell.is_none() {
                    // In case the cell is empty, we can safely get a
                    // unique reference
                    let cell = unsafe { &mut *self.inner.get() };
                    *cell = Some(f()?);

                    // Return cell, converting to shared reference
                    cell
                } else {
                    cell
                }
            };

            Ok(unsafe { cell.as_ref().unwrap_unchecked() })
        })
    }

    /// Consumes the cell, returning the wrapped value.
    ///
    /// Returns `None` if the cell was empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use critical_once_cell::CriticalOnceCell;
    ///
    /// let cell: CriticalOnceCell<String> = CriticalOnceCell::new();
    /// assert_eq!(cell.into_inner(), None);
    ///
    /// let cell = CriticalOnceCell::new();
    /// cell.set("hello".to_string()).unwrap();
    /// assert_eq!(cell.into_inner(), Some("hello".to_string()));
    /// ```
    pub fn into_inner(self) -> Option<T> {
        self.inner.into_inner()
    }

    /// Takes the value out of this `OnceCell`, moving it back to an uninitialized state.
    ///
    /// Has no effect and returns `None` if the `OnceCell` hasn't been initialized.
    ///
    /// Safety is guaranteed by requiring a mutable reference.
    ///
    /// # Examples
    ///
    /// ```
    /// use critical_once_cell::CriticalOnceCell;
    ///
    /// let mut cell: CriticalOnceCell<String> = CriticalOnceCell::new();
    /// assert_eq!(cell.take(), None);
    ///
    /// let mut cell = CriticalOnceCell::new();
    /// cell.set("hello".to_string()).unwrap();
    /// assert_eq!(cell.take(), Some("hello".to_string()));
    /// assert_eq!(cell.get(), None);
    /// ```
    pub fn take(&mut self) -> Option<T> {
        critical_section::with(|_| {
            let cell = unsafe { &mut *self.inner.get() };

            cell.take()
        })
    }
}

unsafe impl<T> Sync for CriticalOnceCell<T> where T: Send + Sync {}

/// A thread-safe value which is initialized on the first access.
///
/// # Examples
///
/// ```
/// use critical_once_cell::CriticalLazy;
///
/// let lazy: CriticalLazy<i32> = CriticalLazy::new(|| {
///     println!("initializing");
///     92
/// });
/// println!("ready");
/// println!("{}", *lazy);
/// println!("{}", *lazy);
///
/// // Prints:
/// //   ready
/// //   initializing
/// //   92
/// //   92
/// ```
pub struct CriticalLazy<T, F = fn() -> T> {
    cell: CriticalOnceCell<T>,
    init: Cell<Option<F>>,
}

impl<T, F> CriticalLazy<T, F> {
    pub const fn new(f: F) -> Self {
        Self {
            cell: CriticalOnceCell::new(),
            init: Cell::new(Some(f)),
        }
    }
}

impl<T, F> CriticalLazy<T, F>
where
    F: FnOnce() -> T,
{
    pub fn force(this: &Self) -> &T {
        this.cell.get_or_init(|| match this.init.take() {
            Some(f) => f(),
            None => panic!("`CriticalLazy` instance has previously been poisoned"),
        })
    }
}

impl<T, F> Deref for CriticalLazy<T, F>
where
    F: FnOnce() -> T,
{
    type Target = T;

    fn deref(&self) -> &Self::Target {
        Self::force(self)
    }
}

unsafe impl<T, F> Sync for CriticalLazy<T, F>
where
    T: Send + Sync,
    F: Send,
{
}

#[cfg(test)]
#[macro_use]
extern crate std;

#[cfg(test)]
mod tests {
    use core::sync::atomic::{AtomicUsize, Ordering};
    use std::thread;

    use std::vec::Vec;

    use std::boxed::Box;

    use std::sync::Arc;

    use super::*;

    #[test]
    fn cell() {
        let mut cell = CriticalOnceCell::new();

        assert!(cell.get().is_none());
        assert!(cell.take().is_none());

        assert!(cell.set(42).is_ok());
        assert_eq!(cell.set(42), Err(42));

        assert_eq!(*cell.get().unwrap(), 42);
        assert_eq!(cell.take(), Some(42));
        assert!(cell.take().is_none());

        assert!(cell.set(43).is_ok());
        assert_eq!(cell.set(43), Err(43));

        assert_eq!(*cell.get().unwrap(), 43);
    }

    #[test]
    fn cell_mut() {
        let mut cell = CriticalOnceCell::new();
        assert!(cell.set(42).is_ok());

        let inner = cell.get_mut().unwrap();

        *inner = 44;

        assert_eq!(*cell.get().unwrap(), 44);
    }

    #[test]
    fn get_or_init() {
        let cell = CriticalOnceCell::new();

        assert_eq!(*cell.get_or_init(|| 42), 42);
        assert_eq!(*cell.get_or_init(|| 43), 42);
    }

    #[test]
    fn get_or_try_init() {
        let cell = CriticalOnceCell::new();

        assert!(cell.get_or_try_init(|| Err(())).is_err());
        assert_eq!(*cell.get_or_try_init::<_, ()>(|| Ok(42)).unwrap(), 42);
        assert_eq!(*cell.get_or_try_init::<_, ()>(|| Ok(43)).unwrap(), 42);
        assert_eq!(*cell.get_or_try_init(|| Err(())).unwrap(), 42);
    }

    #[test]
    fn threads() {
        let cell = Arc::new(CriticalOnceCell::new());

        let handles: Vec<_> = (0..10)
            .map(|i| {
                let cell = cell.clone();

                thread::spawn(move || {
                    let value = Box::new(i);
                    let res = cell.set(value);

                    if res.is_ok() {
                        Some(i)
                    } else {
                        None
                    }
                })
            })
            .collect();

        let values: Vec<_> = handles
            .into_iter()
            .map(|handle| handle.join().unwrap())
            .collect();

        for value in values {
            if let Some(value) = value {
                assert_eq!(value, **cell.get().unwrap());
            }
        }
    }

    #[test]
    fn lazy() {
        let init = Cell::new(0);
        let counter = CriticalLazy::new(|| {
            init.set(init.get() + 1);
            AtomicUsize::new(0)
        });

        for _ in 0..10 {
            counter.fetch_add(1, Ordering::Relaxed);
        }

        assert_eq!(init.get(), 1);
        assert_eq!(counter.load(Ordering::Relaxed), 10);
    }

    #[test]
    fn lazy_threads() {
        const N: usize = 100;
        let counter = Arc::new(CriticalLazy::new(|| AtomicUsize::new(0)));

        let handles: Vec<_> = (0..N)
            .map(|_| {
                let counter = counter.clone();
                thread::spawn(move || {
                    counter.fetch_add(1, Ordering::Relaxed);
                })
            })
            .collect();

        for handle in handles {
            handle.join().unwrap();
        }

        assert_eq!(counter.load(Ordering::Relaxed), N);
    }
}
