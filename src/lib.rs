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
//! # Implementation
//!
//! `Slab` is backed by a `Vec` of slots. Each slot is either occupied or
//! vacant. `Slab` maintains a stack of vacant slots using a linked list. To
//! find a vacant slot, the stack is popped. When a slot is released, it is
//! pushed onto the stack.
//!
//! If there are no more available slots in the stack, then `Vec::reserve(1)` is
//! called and a new slot is created.

use std::{fmt, mem, usize};
use std::iter::IntoIterator;
use std::ops;
use std::marker::PhantomData;

/// A preallocated chunk of memory for storing objects of the same type.
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

pub struct Slot<'a, T: 'a, K: 'a> {
    slab: &'a mut Slab<T, K>,
    key: usize,
}

/// An iterator over the values stored in the `Slab`
pub struct Iter<'a, T: 'a, K: 'a> {
    slab: &'a Slab<T, K>,
    curr: usize,
}

/// A mutable iterator over the values stored in the `Slab`
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
    pub fn new() -> Slab<T, usize> {
        Slab::with_capacity(0)
    }

    /// Returns an empty `Slab` with the requested capacity
    pub fn with_capacity(capacity: usize) -> Slab<T, usize> {
        Slab::with_capacity_and_key_type(capacity)
    }
}

impl<T, K> Slab<T, K> {
    /// Returns an empty `Slab` with the requested capacity
    pub fn with_capacity_and_key_type(capacity: usize) -> Slab<T, K> {
        Slab {
            entries: Vec::with_capacity(capacity),
            next: 0,
            len: 0,
            _marker: PhantomData,
        }
    }

    /// Returns the number of values this slab can store without reallocating.
    ///
    /// # Examples
    ///
    /// ```
    /// println!("Hello");
    /// ```
    pub fn capacity(&self) -> usize {
        self.entries.capacity()
    }

    /// Reserves capacity for at least `additional` more values to be stored
    /// without allocating.
    ///
    /// If the `Slab` is able to store at least `additional` more values, then a
    /// call to `reserve` will do nothing. When additional storage space is
    /// needed, `Slab` will allocate a new slab of memory that is able to store
    /// the current values being stored as well as at least `additional` more
    /// values. The existing values will be copied to the new slab of memory. As
    /// such, if the slab is already large, a call to `reserve` can end up being
    /// relatively expensive.
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
    /// println!("hello");
    /// ```
    pub fn reserve(&mut self, additional: usize) {
        let available = self.entries.len() - self.len;

        if available >= additional {
            return;
        }

        self.entries.reserve(additional - available);
    }

    pub fn reserve_exact(&mut self, additional: usize) {
        let available = self.entries.len() - self.len;

        if available >= additional {
            return;
        }

        self.entries.reserve_exact(additional - available);
    }

    pub fn shrink_to_fit(&mut self) {
        self.entries.shrink_to_fit();
    }

    pub fn clear(&mut self) {
        self.entries.clear();
        self.len = 0;
        self.next = 0;
    }

    /// Returns the number of values stored by the `Slab`
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns true if the `Slab` is storing no values
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn iter(&self) -> Iter<T, K> {
        Iter {
            slab: self,
            curr: 0,
        }
    }

    pub fn iter_mut(&mut self) -> IterMut<T, K> {
        IterMut {
            slab: self as *mut Slab<T, K>,
            curr: 0,
            _marker: PhantomData,
        }
    }
}

impl<T, K: Into<usize> + From<usize>> Slab<T, K> {
    /// Get a reference to the value associated with the given token
    pub fn get(&self, key: K) -> Option<&T> {
        match self.entries[key.into()] {
            Entry::Occupied(ref val) => Some(val),
            Entry::Vacant(..) => None,
        }
    }

    /// Get a mutable reference to the value associated with the given token
    pub fn get_mut(&mut self, key: K) -> Option<&mut T> {
        match self.entries[key.into()] {
            Entry::Occupied(ref mut val) => Some(val),
            Entry::Vacant(..) => None,
        }
    }

    pub unsafe fn get_unchecked(&self, key: K) -> &T {
        match *self.entries.get_unchecked(key.into()) {
            Entry::Occupied(ref val) => val,
            _ => unreachable!(),
        }
    }

    pub unsafe fn get_unchecked_mut(&mut self, key: K) -> &mut T {
        match *self.entries.get_unchecked_mut(key.into()) {
            Entry::Occupied(ref mut val) => val,
            _ => unreachable!(),
        }
    }

    pub fn store(&mut self, val: T) -> K {
        let key = self.next;

        self.store_at(key, val);

        key.into()
    }

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

    /// Releases the given slot
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
    pub fn store(self, val: T) -> &'a mut T {
        self.slab.store_at(self.key, val);

        match self.slab.entries[self.key] {
            Entry::Occupied(ref mut v) => v,
            _ => unreachable!(),
        }
    }

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
