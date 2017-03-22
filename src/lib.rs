//! Pre-allocated storage for a uniform data type.
//!
//! `Slab` provides pre-allocated storage for a single data type. If many values
//! of a single type are being allocated, it can be more efficient to
//! pre-allocate the necessary storage. Since the size of the type is uniform,
//! memory fragmentation can be avoided. Storing, clearing, and lookup
//! operations become very cheap.
//!
//! While `Slab` may look like other Rust collections, it is not intended to be
//! used as a general purpose collection. The primary difference between `Slab`
//! and `Vec` is that `Slab` returns the key when storing the value.
//!
//! It is important to note that keys may be reused. In other words, once a
//! value associated with a given key is removed from a slab, that key may be
//! returned from future calls to `store`.
//!
//! # Examples
//!
//! Basic storing and retrieval.
//!
//! ```
//! # use slab::*;
//! let mut slab = Slab::new();
//!
//! let hello = slab.store("hello");
//! let world = slab.store("world");
//!
//! assert_eq!(slab[hello], "hello");
//! assert_eq!(slab[world], "world");
//!
//! slab[world] = "earth";
//! assert_eq!(slab[world], "earth");
//! ```
//!
//! Sometimes it is useful to be able to associate the key with the value being
//! stored in the slab. This can be done with the `slot` API as such:
//!
//! ```
//! # use slab::*;
//! let mut slab = Slab::new();
//!
//! let hello = {
//!     let slot = slab.slot();
//!     let key = slot.key();
//!
//!     slot.store((key, "hello"));
//!     key
//! };
//!
//! assert_eq!(hello, slab[hello].0);
//! assert_eq!("hello", slab[hello].1);
//! ```
//!
//! It is generally a good idea to specify the desired capacity of a slab at
//! creation time. Note that `Slab` will grow the internal capacity when
//! attempting to store a new value once the existing capacity has been reached.
//! To avoid this, add a check.
//!
//! ```
//! # use slab::*;
//! let mut slab = Slab::with_capacity(1024);
//!
//! // ... use the slab
//!
//! if slab.len() == slab.capacity() {
//!     panic!("slab full");
//! }
//!
//! slab.store("the slab is not at capacity yet");
//! ```
//!
//! # Capacity and reallocation
//!
//! The capacity of a slab is the amount of space allocated for any future
//! values that will be stored in the slab. This is not to be confused with the
//! *length* of the slab, which specifies the number of actual values currently
//! being stored. If a slab's length is equal to its capacity, the next value
//! stored into the slab will require growing the slab by reallocating.
//!
//! For example, a slab with capacity 10 and length 0 would be an empty slab
//! with space for 10 more stored values. Storing 10 or fewer elements into the
//! slab will not change its capacity or cause reallocation to occur. However,
//! if the slab length is increased to 11 (due to another `store`), it will have
//! to reallocate, which can be slow. For this reason, it is recommended to use
//! [`Slab::with_capacity`] whenever possible to specify how many values the
//! slab is expected to store.
//!
//! # Implementation
//!
//! `Slab` is backed by a `Vec` of slots. Each slot is either occupied or
//! vacant. `Slab` maintains a stack of vacant slots using a linked list. To
//! find a vacant slot, the stack is popped. When a slot is released, it is
//! pushed onto the stack.
//!
//! If there are no more available slots in the stack, then `Vec::reserve(1)` is
//! called and a new slot is created.
//!
//! [`Slab::with_capacity`]: struct.Slab.html#with_capacity

#![deny(warnings, missing_docs, missing_debug_implementations)]
#![doc(html_root_url = "https://docs.rs/slab/0.4")]
#![crate_name = "slab"]

use std::{fmt, mem, usize};
use std::iter::IntoIterator;
use std::ops;
use std::marker::PhantomData;

/// Pre-allocated storage for a uniform data type
///
/// See [module documentation] for more details.
///
/// [module documentation]: index.html
#[derive(Clone)]
pub struct Slab<T, K = usize> {
    // Chunk of memory
    entries: Vec<Entry<T>>,

    // Number of Filled elements currently in the slab
    len: usize,

    // Offset of the next available slot in the slab. Set to the slab's
    // capacity when the slab is full.
    next: usize,

    _marker: PhantomData<K>,
}

/// A handle to an empty slot in a `Slab`.
///
/// `Slot` allows constructing values with the key that they will be assigned
/// to.
///
/// # Examples
///
/// ```
/// # use slab::*;
/// let mut slab = Slab::new();
///
/// let hello = {
///     let slot = slab.slot();
///     let key = slot.key();
///
///     slot.store((key, "hello"));
///     key
/// };
///
/// assert_eq!(hello, slab[hello].0);
/// assert_eq!("hello", slab[hello].1);
/// ```
#[derive(Debug)]
pub struct Slot<'a, T: 'a, K: 'a> {
    slab: &'a mut Slab<T, K>,
    key: usize,
}

/// An iterator over the values stored in the `Slab`
#[derive(Debug)]
pub struct Iter<'a, T: 'a, K: 'a> {
    slab: &'a Slab<T, K>,
    curr: usize,
}

/// A mutable iterator over the values stored in the `Slab`
#[derive(Debug)]
pub struct IterMut<'a, T: 'a, K: 'a> {
    slab: *mut Slab<T, K>,
    curr: usize,
    _marker: PhantomData<&'a mut ()>,
}

#[derive(Clone)]
enum Entry<T> {
    Vacant(usize),
    Occupied(T),
}

impl<T> Slab<T, usize> {
    /// Construct a new, empty `Slab`.
    ///
    /// The function does not allocate and the returned slab will have no
    /// capacity until `store` is called or capacity is explicitly reserved.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slab::*;
    /// let slab: Slab<i32> = Slab::new();
    /// ```
    pub fn new() -> Slab<T, usize> {
        Slab::with_capacity(0)
    }

    /// Construct a new, empty `Slab` with the specified capacity.
    ///
    /// The returned slab will be able to store exactly `capacity` without
    /// reallocating. If `capacity` is 0, the slab will not allocate.
    ///
    /// It is important to note that this function does not specify the *length*
    /// of the returned slab, but only the capacity. For an explanation of the
    /// difference between length and capacity, see [Capacity and
    /// reallocation](index.html#capacity-and-reallocation).
    ///
    /// # Examples
    ///
    /// ```
    /// # use slab::*;
    /// let mut slab = Slab::with_capacity(10);
    ///
    /// // The slab contains no values, even though it has capacity for more
    /// assert_eq!(slab.len(), 0);
    ///
    /// // These are all done without reallocating...
    /// for i in 0..10 {
    ///     slab.store(i);
    /// }
    ///
    /// // ...but this may make the slab reallocate
    /// slab.store(11);
    /// ```
    pub fn with_capacity(capacity: usize) -> Slab<T, usize> {
        Slab::with_capacity_and_key_type(capacity)
    }
}

impl<T, K> Slab<T, K> {
    /// Construct a new, empty `Slab` with the specified capacity using a custom
    /// key type.
    ///
    /// This function is identical to [with_capacity] except that it also allows
    /// the slab to use a custom key type.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slab::*;
    /// #[derive(Debug, Eq, PartialEq)]
    /// struct MyKey(usize);
    ///
    /// impl From<usize> for MyKey {
    ///     fn from(i: usize) -> MyKey { MyKey(i) }
    /// }
    ///
    /// impl Into<usize> for MyKey {
    ///     fn into(self) -> usize { self.0 }
    /// }
    ///
    /// let mut slab = Slab::with_capacity_and_key_type(1);
    /// let key: MyKey = slab.store(10);
    ///
    /// assert_eq!(key, MyKey(0));
    /// assert_eq!(slab[key], 10);
    /// ```
    ///
    /// [with_capacity]: #with_capacity
    pub fn with_capacity_and_key_type(capacity: usize) -> Slab<T, K> {
        Slab {
            entries: Vec::with_capacity(capacity),
            next: 0,
            len: 0,
            _marker: PhantomData,
        }
    }

    /// Returns the number of values the slab can store without reallocating.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slab::*;
    /// let slab: Slab<i32> = Slab::with_capacity(10);
    /// assert_eq!(slab.capacity(), 10);
    /// ```
    pub fn capacity(&self) -> usize {
        self.entries.capacity()
    }

    /// Reserves capacity for at least `additional` more values to be stored
    /// without allocating.
    ///
    /// `reserve` does nothing if the slab already has sufficient capcity for
    /// `additional` more values. If more capacity is required, a new segment of
    /// memory will be allocated and all existing values will be copied into it.
    /// As such, if the slab is already very large, a call to `reserve` can end
    /// up being expensive.
    ///
    /// The slab may reserve more than `additional` extra space in order to
    /// avoid frequent reallocations. Use `reserve_exact` instead to guarantee
    /// that only the requested space is allocated.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows `usize`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slab::*;
    /// let mut slab = Slab::new();
    /// slab.store("hello");
    /// slab.reserve(10);
    /// assert!(slab.capacity() >= 11);
    /// ```
    pub fn reserve(&mut self, additional: usize) {
        let available = self.entries.len() - self.len;

        if available >= additional {
            return;
        }

        self.entries.reserve(additional - available);
    }

    /// Reserves the minimum capacity required to store exactly `additional`
    /// more values.
    ///
    /// `reserve_exact` does nothing if the slab already has sufficient capacity
    /// for `additional` more valus. If more capacity is required, a new segment
    /// of memory will be allocated and all existing values will be copied into
    /// it.  As such, if the slab is already very large, a call to `reserve` can
    /// end up being expensive.
    ///
    /// Note that the allocator may give the slab more space than it requests.
    /// Therefore capacity can not be relied upon to be precisely minimal.
    /// Prefer `reserve` if future insertions are expected.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows `usize`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slab::*;
    /// let mut slab = Slab::new();
    /// slab.store("hello");
    /// slab.reserve_exact(10);
    /// assert!(slab.capacity() >= 11);
    /// ```
    pub fn reserve_exact(&mut self, additional: usize) {
        let available = self.entries.len() - self.len;

        if available >= additional {
            return;
        }

        self.entries.reserve_exact(additional - available);
    }

    /// Shrinks the capacity of the slab as much as possible.
    ///
    /// It will drop down as close as possible to the length but the allocator
    /// may still inform the vector that there is space for a few more elements.
    /// Also, since values are not moved, the slab cannot shrink past any stored
    /// values.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slab::*;
    /// let mut slab = Slab::with_capacity(10);
    ///
    /// for i in 0..3 {
    ///     slab.store(i);
    /// }
    ///
    /// assert_eq!(slab.capacity(), 10);
    /// slab.shrink_to_fit();
    /// assert!(slab.capacity() >= 3);
    /// ```
    ///
    /// In this case, even though two values are removed, the slab cannot shrink
    /// past the last value.
    ///
    /// ```
    /// # use slab::*;
    /// let mut slab = Slab::with_capacity(10);
    ///
    /// for i in 0..3 {
    ///     slab.store(i);
    /// }
    ///
    /// slab.remove(0);
    /// slab.remove(1);
    ///
    /// assert_eq!(slab.capacity(), 10);
    /// slab.shrink_to_fit();
    /// assert!(slab.capacity() >= 3);
    /// ```
    pub fn shrink_to_fit(&mut self) {
        self.entries.shrink_to_fit();
    }

    /// Clear the slab of all values
    ///
    /// # Examples
    ///
    /// ```
    /// # use slab::*;
    /// let mut slab = Slab::new();
    ///
    /// for i in 0..3 {
    ///     slab.store(i);
    /// }
    ///
    /// slab.clear();
    /// assert!(slab.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.entries.clear();
        self.len = 0;
        self.next = 0;
    }

    /// Returns the number of stored values
    ///
    /// # Examples
    ///
    /// ```
    /// # use slab::*;
    /// let mut slab = Slab::new();
    ///
    /// for i in 0..3 {
    ///     slab.store(i);
    /// }
    ///
    /// assert_eq!(3, slab.len());
    /// ```
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns `true` if no values are stored in the slab
    ///
    /// # Examples
    ///
    /// ```
    /// # use slab::*;
    /// let mut slab = Slab::new();
    /// assert!(slab.is_empty());
    ///
    /// slab.store(1);
    /// assert!(!slab.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Returns an iterator over the slab
    ///
    /// This function should generally be **avoided** as it is not efficient.
    /// Iterators must iterate over every slot in the slab even if it is
    /// vaccant. As such, a slab with a capacity of 1 million but only one
    /// stored value must still iterate the million slots.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slab::*;
    /// let mut slab = Slab::new();
    ///
    /// for i in 0..3 {
    ///     slab.store(i);
    /// }
    ///
    /// let mut iterator = slab.iter();
    ///
    /// assert_eq!(iterator.next(), Some(&0));
    /// assert_eq!(iterator.next(), Some(&1));
    /// assert_eq!(iterator.next(), Some(&2));
    /// assert_eq!(iterator.next(), None);
    /// ```
    pub fn iter(&self) -> Iter<T, K> {
        Iter {
            slab: self,
            curr: 0,
        }
    }

    /// Returns an iterator that allows modifying each value.
    ///
    /// This function should generally be **avoided** as it is not efficient.
    /// Iterators must iterate over every slot in the slab even if it is
    /// vaccant. As such, a slab with a capacity of 1 million but only one
    /// stored value must still iterate the million slots.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slab::*;
    /// let mut slab = Slab::new();
    ///
    /// let key1 = slab.store(0);
    /// let key2 = slab.store(1);
    ///
    /// for val in slab.iter_mut() {
    ///     *val += 2;
    /// }
    ///
    /// assert_eq!(slab[key1], 2);
    /// assert_eq!(slab[key2], 3);
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<T, K> {
        IterMut {
            slab: self as *mut Slab<T, K>,
            curr: 0,
            _marker: PhantomData,
        }
    }
}

impl<T, K: Into<usize> + From<usize>> Slab<T, K> {
    /// Returns a reference to the value associated with the given key
    ///
    /// If the given key is not associated with a value, then `None` is
    /// returned.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slab::*;
    /// let mut slab = Slab::new();
    /// let key = slab.store("hello");
    ///
    /// assert_eq!(slab.get(key), Some(&"hello"));
    /// assert_eq!(slab.get(123), None);
    /// ```
    pub fn get(&self, key: K) -> Option<&T> {
        match self.entries.get(key.into()) {
            Some(&Entry::Occupied(ref val)) => Some(val),
            _ => None,
        }
    }

    /// Returns a mutable reference to the value associated with the given key
    ///
    /// If the given key is not associated with a value, then `None` is
    /// returned.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slab::*;
    /// let mut slab = Slab::new();
    /// let key = slab.store("hello");
    ///
    /// *slab.get_mut(key).unwrap() = "world";
    ///
    /// assert_eq!(slab[key], "world");
    /// assert_eq!(slab.get_mut(123), None);
    /// ```
    pub fn get_mut(&mut self, key: K) -> Option<&mut T> {
        match self.entries.get_mut(key.into()) {
            Some(&mut Entry::Occupied(ref mut val)) => Some(val),
            _ => None,
        }
    }

    /// Returns a reference to the value associated with the given key without
    /// performing bounds checking.
    ///
    /// This function should be used with care.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slab::*;
    /// let mut slab = Slab::new();
    /// let key = slab.store(2);
    ///
    /// unsafe {
    ///     assert_eq!(slab.get_unchecked(key), &2);
    /// }
    /// ```
    pub unsafe fn get_unchecked(&self, key: K) -> &T {
        match *self.entries.get_unchecked(key.into()) {
            Entry::Occupied(ref val) => val,
            _ => unreachable!(),
        }
    }

    /// Returns a mutable reference to the value associated with the given key
    /// without performing bounds checking.
    ///
    /// This function should be used with care.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slab::*;
    /// let mut slab = Slab::new();
    /// let key = slab.store(2);
    ///
    /// unsafe {
    ///     let val = slab.get_unchecked_mut(key);
    ///     *val = 13;
    /// }
    ///
    /// assert_eq!(slab[key], 13);
    /// ```
    pub unsafe fn get_unchecked_mut(&mut self, key: K) -> &mut T {
        match *self.entries.get_unchecked_mut(key.into()) {
            Entry::Occupied(ref mut val) => val,
            _ => unreachable!(),
        }
    }

    /// Store a value in the slab, returning key assigned to the value
    ///
    /// The returned key can later be used to retrieve or remove the value using indexed
    /// lookup and `remove`. Additional capacity is allocated if needed. See
    /// [Capacity and reallocation](index.html#capacity-and-reallocation).
    ///
    /// # Panics
    ///
    /// Panics if the number of elements in the vector overflows a `usize`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slab::*;
    /// let mut slab = Slab::new();
    /// let key = slab.store("hello");
    /// assert_eq!(slab[key], "hello");
    /// ```
    pub fn store(&mut self, val: T) -> K {
        let key = self.next;

        self.store_at(key, val);

        key.into()
    }

    /// Returns a handle to a vaccant slot allowing for further manipulation.
    pub fn slot(&mut self) -> Slot<T, K> {
        Slot {
            key: self.next,
            slab: self,
        }
    }

    /// Store the value at the given key
    fn store_at(&mut self, key: usize, val: T) {
        self.len += 1;

        if key == self.entries.len() {
            self.entries.push(Entry::Occupied(val));
            self.next = key + 1;
        } else {
            let prev = mem::replace(
                &mut self.entries[key],
                Entry::Occupied(val));

            match prev {
                Entry::Vacant(next) => {
                    self.next = next;
                }
                _ => unreachable!(),
            }
        }
    }

    /// Removes and returns the value associated with the given key.
    ///
    /// The key is then released and may be associated with future stored
    /// values.
    pub fn remove(&mut self, key: K) -> T {
        let key = key.into();

        // Swap the entry at the provided value
        let prev = mem::replace(
            &mut self.entries[key],
            Entry::Vacant(self.next));

        match prev {
            Entry::Occupied(val) => {
                self.len -= 1;
                self.next = key;
                val
            }
            _ => {
                // Woops, the entry is actually vacant, restore the state
                self.entries[key] = prev;
                panic!("invalid key");
            }
        }
    }

    /// Returns `true` if a value is associated with the given key.
    pub fn contains(&self, key: K) -> bool {
        self.entries.get(key.into())
            .map(|e| {
                match *e {
                    Entry::Occupied(_) => true,
                    _ => false,
                }
            })
            .unwrap_or(false)
    }

    /// Retain only the elements specified by the predicate.
    ///
    /// In other words, remove all elements `e` such that `f(&e)` returns false.
    /// This method operates in place and preserves the order of the retained
    /// elements.
    pub fn retain<F>(&mut self, mut f: F)
        where F: FnMut(&T) -> bool
    {
        for i in 0..self.entries.len() {
            let keep = match self.entries[i] {
                Entry::Occupied(ref v) => f(v),
                _ => true,
            };

            if !keep {
                self.remove(i.into());
            }
        }
    }
}

impl<T, K> ops::Index<K> for Slab<T, K>
    where K: From<usize> + Into<usize>,
{
    type Output = T;

    fn index(&self, key: K) -> &T {
        match self.entries[key.into()] {
            Entry::Occupied(ref v) => v,
            _ => panic!("invalid key"),
        }
    }
}

impl<T, K> ops::IndexMut<K> for Slab<T, K>
    where K: From<usize> + Into<usize>,
{
    fn index_mut(&mut self, key: K) -> &mut T {
        match self.entries[key.into()] {
            Entry::Occupied(ref mut v) => v,
            _ => panic!("invalid key"),
        }
    }
}

impl<'a, T, K> IntoIterator for &'a Slab<T, K> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T, K>;

    fn into_iter(self) -> Iter<'a, T, K> {
        self.iter()
    }
}

impl<'a, T, K> IntoIterator for &'a mut Slab<T, K> {
    type Item = &'a mut T;
    type IntoIter = IterMut<'a, T, K>;

    fn into_iter(self) -> IterMut<'a, T, K> {
        self.iter_mut()
    }
}

impl<T, K> fmt::Debug for Slab<T, K>
    where T: fmt::Debug,
          K: fmt::Debug,
{
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt,
               "Slab {{ len: {}, cap: {} }}",
               self.len,
               self.capacity())
    }
}

// ===== Slot =====

impl<'a, T, K> Slot<'a, T, K>
    where K: From<usize> + Into<usize>,
{
    /// Store a value in the slot, returning a mutable reference to the value.
    ///
    /// To get the key associated with the value, use `key` prior to calling
    /// `store`.
    pub fn store(self, val: T) -> &'a mut T {
        self.slab.store_at(self.key, val);

        match self.slab.entries[self.key] {
            Entry::Occupied(ref mut v) => v,
            _ => unreachable!(),
        }
    }

    /// Return the key associated with this slot.
    ///
    /// A value stored in this slot will be associated with this key.
    pub fn key(&self) -> K {
        self.key.into()
    }
}

// ===== Iter =====

impl<'a, T, K> Iterator for Iter<'a, T, K> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        while self.curr < self.slab.entries.len() {
            let curr = self.curr;
            self.curr += 1;

            if let Entry::Occupied(ref v) = self.slab.entries[curr] {
                return Some(v);
            }
        }

        None
    }
}

// ===== IterMut =====

impl<'a, T, K> Iterator for IterMut<'a, T, K> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<&'a mut T> {
        unsafe {
            while self.curr < (*self.slab).entries.len() {
                let curr = self.curr;
                self.curr += 1;

                if let Entry::Occupied(ref mut v) = (*self.slab).entries[curr] {
                    return Some(v);
                }
            }

            None
        }
    }
}
