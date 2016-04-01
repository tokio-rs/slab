use std::{fmt, mem, usize};
use std::iter::IntoIterator;
use std::ops;
use std::marker::PhantomData;

/// A preallocated chunk of memory for storing objects of the same type.
pub struct Slab<T, I: Index> {
    // Chunk of memory
    entries: Vec<Slot<T>>,

    // Number of Filled elements currently in the slab
    len: usize,

    // The index offset
    offset: usize,

    // Offset of the next available slot in the slab. Set to the slab's
    // capacity when the slab is full.
    next: usize,

    _marker: PhantomData<I>,
}

enum Slot<T> {
    Empty(usize),
    Filled(T),
}

// Need this for Rust 1.0 compatibility
// See: https://github.com/rust-lang/rust/issues/15609
impl<T> Slot<T> {
    #[inline]
    fn as_mut(&mut self) -> Option<&mut T> {
        match *self {
            Slot::Filled(ref mut val) => Some(val),
            Slot::Empty(_) => None,
        }
    }
}

/// Slab can be indexed by any type implementing `Index` trait.
pub trait Index {
    fn from_usize(i: usize) -> Self;

    fn as_usize(&self) -> usize;
}

impl Index for usize {
    fn from_usize(i: usize) -> usize {
        i
    }

    fn as_usize(&self) -> usize {
        *self
    }
}

unsafe impl<T, I: Index> Send for Slab<T, I> where T: Send {}

macro_rules! some {
    ($expr:expr) => (match $expr {
        Some(val) => val,
        None => return None,
    })
}

impl<T, I: Index> Slab<T, I> {
    #[inline]
    pub fn new(capacity: usize) -> Slab<T, I> {
        Slab::new_starting_at(I::from_usize(0), capacity)
    }

    pub fn new_starting_at(offset: I, capacity: usize) -> Slab<T, I> {
        assert!(capacity <= usize::MAX, "capacity too large");
        let entries = (1..capacity + 1)
            .map(Slot::Empty)
            .collect::<Vec<_>>();

        Slab {
            entries: entries,
            next: 0,
            len: 0,
            offset: offset.as_usize(),
            _marker: PhantomData,
        }
    }

    #[inline]
    pub fn count(&self) -> usize {
        self.len
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    #[inline]
    pub fn remaining(&self) -> usize {
        self.entries.capacity() - self.len
    }

    #[inline]
    pub fn has_remaining(&self) -> bool {
        self.remaining() > 0
    }

    #[inline]
    pub fn contains(&self, idx: I) -> bool {
        self.get(idx).is_some()
    }

    #[inline]
    pub fn get(&self, idx: I) -> Option<&T> {
        let idx = some!(self.local_index(idx));

        match self.entries[idx] {
            Slot::Filled(ref val) => Some(val),
            Slot::Empty(_) => None,
        }
    }

    #[inline]
    pub fn get_mut(&mut self, idx: I) -> Option<&mut T> {
        let idx = some!(self.local_index(idx));

        return self.entries[idx].as_mut();
    }

    #[inline]
    pub fn insert(&mut self, val: T) -> Result<I, T> {
        match self.vacant_entry() {
            Some(entry) => Ok(entry.insert(val).index()),
            None => Err(val),
        }
    }

    pub fn vacant_entry(&mut self) -> Option<VacantEntry<I, T>> {
        let idx = self.next;

        if idx >= self.entries.len() {
            return None;
        }

        let idx = idx + self.offset;

        Some(VacantEntry {
            slab: self,
            idx: idx,
        })
    }

    pub fn entry(&mut self, idx: I) -> Option<Entry<I, T>> {
        let local_idx = some!(self.local_index(idx));
        let idx = local_idx + self.offset;

        Some(match self.entries[local_idx] {
            Slot::Empty(_) => {
                Entry::Vacant(VacantEntry {
                    slab: self,
                    idx: idx,
                })
            }

            Slot::Filled(_) => {
                Entry::Occupied(OccupiedEntry {
                    slab: self,
                    idx: idx,
                })
            }
        })
    }

    /// Like `insert` but for objects that require newly allocated
    /// usize in their constructor.
    ///
    /// NOTE: This method is deprecated in favor of the `entry` API.
    #[inline]
    pub fn insert_with<F>(&mut self, fun: F) -> Option<I>
        where F: FnOnce(I) -> T
    {
        let entry = some!(self.vacant_entry());
        let idx = entry.index();
        Some(entry.insert(fun(idx)).index())
    }

    /// Like `insert_with` but allows function to return nothing instead of
    /// a value.
    ///
    /// This is useful for mio when you need a token to register a socket
    /// but socket registration might fail so you don't have anything useful
    /// to insert.
    ///
    /// NOTE: This method is deprecated in favor of the `entry` API.
    #[inline]
    pub fn insert_with_opt<F>(&mut self, fun: F) -> Option<I>
        where F: FnOnce(I) -> Option<T>
    {
        let entry = some!(self.vacant_entry());
        let idx = entry.index();
        let newval = some!(fun(idx));
        Some(entry.insert(newval).index())
    }

    /// Releases the given slot
    #[inline]
    pub fn remove(&mut self, idx: I) -> Option<T> {
        let idx = some!(self.local_index(idx));
        let next = self.next;

        // replace this slot with Empty if it was not already Empty
        if let Slot::Filled(_) = self.entries[idx] {
            self.len -= 1;
            self.replace_(idx, Slot::Empty(next))
        } else {
            None
        }
    }

    /// Replace the given slot, if the slot being replaced was empty,
    /// then we increment the len of the slab
    #[inline]
    pub fn replace(&mut self, idx: I, t : T) -> Option<T> {
        let idx = some!(self.local_index(idx));
        let entry = self.replace_(idx, Slot::Filled(t));

        if entry.is_none() {
            self.len += 1;
        }
        entry
    }

    /// Execute a function on the *value* in the slot and put the result of
    /// the function back into the slot. If function returns None,
    /// slot is left empty on exit.
    ///
    /// Returns Err(()) if slot was empty
    ///
    /// This method is very useful for storing state machines inside Slab
    ///
    /// NOTE: This method is deprecated in favor of the `entry` API.
    #[inline]
    pub fn replace_with<F>(&mut self, idx: I, fun: F) -> Result<(), ()>
        where F: FnOnce(T) -> Option<T>
    {
        match self.entry(idx) {
            None => Err(()),
            Some(Entry::Vacant(_)) => Err(()),
            Some(Entry::Occupied(entry)) => {
                entry.replace_with(fun);
                Ok(())
            }
        }
    }

    /// Retain only the elements specified by the predicate.
    ///
    /// In other words, remove all elements `e` such that `f(&e)` returns false.
    /// This method operates in place and preserves the order of the retained
    /// elements.
    pub fn retain<F>(&mut self, mut fun: F)
        where F: FnMut(&T) -> bool
    {
        for i in 0..self.len {
            let idx = I::from_usize(i + self.offset);

            let _ = self.replace_with(idx, |x| {
                if fun(&x) {
                    Some(x)
                } else {
                    None
                }
            });
        }
    }

    #[inline]
    pub fn iter(&self) -> SlabIter<T, I> {
        SlabIter {
            slab: self,
            cur_idx: 0,
            yielded: 0,
        }
    }

    #[inline]
    pub fn iter_mut(&mut self) -> SlabMutIter<T, I> {
        SlabMutIter { iter: self.iter() }
    }

    /// Empty the slab, by freeing all entries
    pub fn clear(&mut self) {
        for (i, e) in self.entries.iter_mut().enumerate() {
            *e = Slot::Empty(i + 1)
        }
        self.next = 0;
        self.len = 0;
    }

    /// Grow the slab, by adding `entries_num`
    pub fn grow(&mut self, entries_num: usize) {
        let prev_len = self.entries.len();
        let prev_len_next = prev_len + 1;
        self.entries.extend((prev_len_next..(prev_len_next + entries_num)).map(|n| Slot::Empty(n)));
        debug_assert_eq!(self.entries.len(), prev_len + entries_num);
    }

    fn insert_at(&mut self, idx: usize, value: T) -> I {
        let idx = idx - self.offset;

        self.next = match self.entries[idx] {
            Slot::Empty(next) => next,
            Slot::Filled(_) => panic!("Tried to insert into filled index"),
        };

        self.entries[idx] = Slot::Filled(value);
        self.len += 1;

        I::from_usize(idx + self.offset)
    }

    fn local_index(&self, idx: I) -> Option<usize> {
        let idx = idx.as_usize();

        if idx < self.offset {
            return None;
        }

        let idx = idx - self.offset;

        if idx >= self.entries.capacity() {
            return None;
        }

        Some(idx)
    }

    #[inline]
    fn replace_(&mut self, local_idx: usize, e: Slot<T>) -> Option<T> {
        if let Slot::Filled(val) = mem::replace(&mut self.entries[local_idx], e) {
            self.next = local_idx;
            return Some(val);
        }

        None
    }
}

pub enum Entry<'slab, I: Index + 'slab, T: 'slab> {
    Vacant(VacantEntry<'slab, I, T>),
    Occupied(OccupiedEntry<'slab, I, T>),
}

impl<'slab, I: Index, T> Entry<'slab, I, T> {
    #[inline]
    pub fn or_insert(self, default: T) -> &'slab mut T {
        match self {
            Entry::Occupied(o) => o.into_mut(),
            Entry::Vacant(v) => v.insert(default).into_mut(),
        }
    }

    #[inline]
    pub fn or_insert_with<F>(self, fun: F) -> &'slab mut T
        where F: FnOnce(I) -> T
    {
        let idx = self.index();

        match self {
            Entry::Occupied(o) => o.into_mut(),
            Entry::Vacant(v) => v.insert(fun(idx)).into_mut(),
        }
    }

    #[inline]
    pub fn or_insert_with_opt<F>(self, fun: F) -> Option<&'slab mut T>
        where F: FnOnce(I) -> Option<T>
    {
        let idx = self.index();

        Some(match self {
            Entry::Occupied(o) => o.into_mut(),
            Entry::Vacant(v) => v.insert(some!(fun(idx))).into_mut(),
        })
    }

    #[inline]
    pub fn index(&self) -> I {
        match *self {
            Entry::Occupied(ref o) => o.index(),
            Entry::Vacant(ref v) => v.index(),
        }
    }
}

pub struct VacantEntry<'slab, I: Index + 'slab, T: 'slab> {
    slab: &'slab mut Slab<T, I>,
    idx: usize,
}

impl<'slab, I: Index, T> VacantEntry<'slab, I, T> {
    #[inline]
    pub fn insert(self, val: T) -> OccupiedEntry<'slab, I, T> {
        self.slab.insert_at(self.idx, val);

        OccupiedEntry {
            slab: self.slab,
            idx: self.idx,
        }
    }

    #[inline]
    pub fn index(&self) -> I {
        I::from_usize(self.idx)
    }
}

pub struct OccupiedEntry<'slab, I: Index + 'slab, T: 'slab> {
    slab: &'slab mut Slab<T, I>,
    idx: usize,
}

impl<'slab, I: Index, T> OccupiedEntry<'slab, I, T> {
    pub fn replace_with<F>(self, fun: F) -> Entry<'slab, I, T>
        where F: FnOnce(T) -> Option<T>
    {
        let (val, vacant) = self.remove();

        let newval = match fun(val) {
            Some(val) => val,
            None => return Entry::Vacant(vacant),
        };

        // Reinsert the new value.
        Entry::Occupied(vacant.insert(newval))
    }

    #[inline]
    pub fn remove(self) -> (T, VacantEntry<'slab, I, T>) {
        let idx = self.index();
        let val = self.slab
                      .remove(idx)
                      .expect("Filled slot in OccupiedEntry");
        let vacant = VacantEntry {
            slab: self.slab,
            idx: self.idx,
        };

        (val, vacant)
    }

    #[inline]
    pub fn get(&self) -> &T {
        let idx = self.index();
        self.slab
            .get(idx)
            .expect("Filled slot in OccupiedEntry")
    }

    #[inline]
    pub fn get_mut(&mut self) -> &mut T {
        let idx = self.index();
        self.slab
            .get_mut(idx)
            .expect("Filled slot in OccupiedEntry")
    }

    pub fn into_mut(self) -> &'slab mut T {
        let idx = self.index();
        self.slab
            .get_mut(idx)
            .expect("Filled slot in OccupiedEntry")
    }

    #[inline]
    pub fn index(&self) -> I {
        I::from_usize(self.idx)
    }
}

impl<T, I: Index> ops::Index<I> for Slab<T, I> {
    type Output = T;

    fn index(&self, index: I) -> &T {
        self.get(index).expect("invalid index")
    }
}

impl<T, I: Index> ops::IndexMut<I> for Slab<T, I> {
    fn index_mut(&mut self, index: I) -> &mut T {
        self.get_mut(index).expect("invalid index")
    }
}

impl<T, I: Index> fmt::Debug for Slab<T, I> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt,
               "Slab {{ len: {}, cap: {} }}",
               self.len,
               self.entries.len())
    }
}

pub struct SlabIter<'a, T: 'a, I: Index + 'a> {
    slab: &'a Slab<T, I>,
    cur_idx: usize,
    yielded: usize,
}

impl<'a, T, I: Index> Iterator for SlabIter<'a, T, I> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        while self.yielded < self.slab.len {
            match self.slab.entries[self.cur_idx] {
                Slot::Filled(ref v) => {
                    self.cur_idx += 1;
                    self.yielded += 1;
                    return Some(v);
                }
                Slot::Empty(_) => {
                    self.cur_idx += 1;
                }
            }
        }

        None
    }
}

pub struct SlabMutIter<'a, T: 'a, I: Index + 'a> {
    iter: SlabIter<'a, T, I>,
}

impl<'a, T, I: Index> Iterator for SlabMutIter<'a, T, I> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<&'a mut T> {
        unsafe { mem::transmute(self.iter.next()) }
    }
}

impl<'a, T, I: Index> IntoIterator for &'a Slab<T, I> {
    type Item = &'a T;
    type IntoIter = SlabIter<'a, T, I>;

    fn into_iter(self) -> SlabIter<'a, T, I> {
        self.iter()
    }
}

impl<'a, T, I: Index> IntoIterator for &'a mut Slab<T, I> {
    type Item = &'a mut T;
    type IntoIter = SlabMutIter<'a, T, I>;

    fn into_iter(self) -> SlabMutIter<'a, T, I> {
        self.iter_mut()
    }
}

#[cfg(test)]
mod tests {
    use super::{Slab, Entry};

    #[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct MyIndex(pub usize);

    impl super::Index for MyIndex {
        fn from_usize(i: usize) -> MyIndex {
            MyIndex(i)
        }

        fn as_usize(&self) -> usize {
            let MyIndex(inner) = *self;
            inner
        }
    }

    #[test]
    fn test_index_trait() {
        let mut slab = Slab::<usize, MyIndex>::new(1);
        let idx = slab.insert(10).ok().expect("Failed to insert");
        assert_eq!(idx, MyIndex(0));
        assert_eq!(slab[idx], 10);
    }

    #[test]
    fn test_insertion() {
        let mut slab = Slab::<usize, usize>::new(1);
        assert_eq!(slab.is_empty(), true);
        assert_eq!(slab.has_remaining(), true);
        assert_eq!(slab.remaining(), 1);
        let idx = slab.insert(10).ok().expect("Failed to insert");
        assert_eq!(slab[idx], 10);
        assert_eq!(slab.is_empty(), false);
        assert_eq!(slab.has_remaining(), false);
        assert_eq!(slab.remaining(), 0);
    }

    #[test]
    fn test_insert_with() {
        let mut slab = Slab::<usize, usize>::new_starting_at(1, 1);
        let tok = slab.insert_with(|_t| 5).unwrap();
        assert_eq!(slab.get(0), None);
        assert_eq!(slab.get_mut(0), None);
        assert_eq!(tok, 1);
    }

    #[test]
    fn test_insert_with_opt() {
        let mut slab = Slab::<usize, usize>::new_starting_at(1, 2);
        let tok = slab.insert_with_opt(|_t| Some(5)).unwrap();
        assert_eq!(tok, 1);
        assert_eq!(slab.get(1), Some(&5));
        assert_eq!(slab.get_mut(1), Some(&mut 5));
        let tok = slab.insert_with_opt(|_t| None);
        assert_eq!(tok, None);
        assert_eq!(slab.get(1), Some(&5));
        assert_eq!(slab.get(2), None);
        let tok = slab.insert(6).unwrap();
        assert_eq!(tok, 2);
        assert_eq!(slab.get(2), Some(&6));
    }

    #[test]
    fn test_repeated_insertion() {
        let mut slab = Slab::<usize, usize>::new(10);

        for i in 0..10 {
            let idx = slab.insert(i + 10).ok().expect("Failed to insert");
            assert_eq!(slab[idx], i + 10);
        }

        slab.insert(20).err().expect("Inserted when full");
    }

    #[test]
    fn test_repeated_insertion_and_removal() {
        let mut slab = Slab::<usize, usize>::new(10);
        let mut indices = vec![];

        for i in 0..10 {
            let idx = slab.insert(i + 10).ok().expect("Failed to insert");
            indices.push(idx);
            assert_eq!(slab[idx], i + 10);
        }

        for &i in indices.iter() {
            slab.remove(i);
        }

        slab.insert(20).ok().expect("Failed to insert in newly empty slab");
    }

    #[test]
    fn test_insertion_when_full() {
        let mut slab = Slab::<usize, usize>::new(1);
        slab.insert(10).ok().expect("Failed to insert");
        slab.insert(10).err().expect("Inserted into a full slab");
    }

    #[test]
    fn test_removal_at_boundries() {
        let mut slab = Slab::<usize, usize>::new(1);
        assert_eq!(slab.remove(0), None);
        assert_eq!(slab.remove(1), None);
    }

    #[test]
    fn test_removal_is_successful() {
        let mut slab = Slab::<usize, usize>::new(1);
        let t1 = slab.insert(10).ok().expect("Failed to insert");
        slab.remove(t1);
        let t2 = slab.insert(20).ok().expect("Failed to insert");
        assert_eq!(slab[t2], 20);
    }

    #[test]
    fn test_remove_empty_entry() {
        let mut s = Slab::<(), usize>::new_starting_at(0, 3);
        let t1 = s.insert(()).unwrap();
        assert!(s.remove(t1).is_some());
        assert!(s.remove(t1).is_none());
        assert!(s.insert(()).is_ok());
        assert!(s.insert(()).is_ok());
    }

    #[test]
    fn test_mut_retrieval() {
        let mut slab = Slab::<_, usize>::new(1);
        let t1 = slab.insert("foo".to_string()).ok().expect("Failed to insert");

        slab[t1].push_str("bar");

        assert_eq!(&slab[t1][..], "foobar");
    }

    #[test]
    #[should_panic]
    fn test_reusing_slots_1() {
        let mut slab = Slab::<usize, usize>::new(16);

        let t0 = slab.insert(123).unwrap();
        let t1 = slab.insert(456).unwrap();

        assert!(slab.count() == 2);
        assert!(slab.remaining() == 14);

        slab.remove(t0);

        assert!(slab.count() == 1, "actual={}", slab.count());
        assert!(slab.remaining() == 15);

        slab.remove(t1);

        assert!(slab.count() == 0);
        assert!(slab.remaining() == 16);

        let _ = slab[t1];
    }

    #[test]
    fn test_reusing_slots_2() {
        let mut slab = Slab::<usize, usize>::new(16);

        let t0 = slab.insert(123).unwrap();

        assert!(slab[t0] == 123);
        assert!(slab.remove(t0) == Some(123));

        let t0 = slab.insert(456).unwrap();

        assert!(slab[t0] == 456);

        let t1 = slab.insert(789).unwrap();

        assert!(slab[t0] == 456);
        assert!(slab[t1] == 789);

        assert!(slab.remove(t0).unwrap() == 456);
        assert!(slab.remove(t1).unwrap() == 789);

        assert!(slab.count() == 0);
    }

    #[test]
    #[should_panic]
    fn test_accessing_out_of_bounds() {
        let slab = Slab::<usize, usize>::new(16);
        slab[0];
    }

    #[test]
    fn test_contains() {
        let mut slab = Slab::new_starting_at(5, 16);
        assert!(!slab.contains(0));

        let idx = slab.insert(111).unwrap();
        assert!(slab.contains(idx));
    }

    #[test]
    fn test_get() {
        let mut slab = Slab::<usize, usize>::new(16);
        let tok = slab.insert(5).unwrap();
        assert_eq!(slab.get(tok), Some(&5));
        assert_eq!(slab.get(1), None);
        assert_eq!(slab.get(23), None);
    }

    #[test]
    fn test_get_mut() {
        let mut slab = Slab::<u32, usize>::new(16);
        let tok = slab.insert(5u32).unwrap();
        {
            let mut_ref = slab.get_mut(tok).unwrap();
            assert_eq!(*mut_ref, 5);
            *mut_ref = 12;
        }
        assert_eq!(slab[tok], 12);
        assert_eq!(slab.get_mut(1), None);
        assert_eq!(slab.get_mut(23), None);
    }

    #[test]
    fn test_index_with_starting_at() {
        let mut slab = Slab::<usize, usize>::new_starting_at(1, 1);
        let tok = slab.insert(5).unwrap();
        assert_eq!(slab.get(0), None);
        assert_eq!(slab.get_mut(0), None);
        assert_eq!(tok, 1);
    }

    #[test]
    fn test_replace() {
        let mut slab = Slab::<usize, usize>::new(16);
        let tok = slab.insert(5).unwrap();
        assert!(slab.replace(tok, 6).is_some());
        assert!(slab.replace(tok + 1, 555).is_none());
        assert_eq!(slab[tok], 6);
        assert_eq!(slab.count(), 2);
    }

    #[test]
    fn test_replace_again() {
        let mut slab = Slab::<usize, usize>::new(16);
        let tok = slab.insert(5).unwrap();
        assert!(slab.replace(tok, 6).is_some());
        assert!(slab.replace(tok, 7).is_some());
        assert!(slab.replace(tok, 8).is_some());
        assert!(slab.replace(tok + 1, 555).is_none());
        assert_eq!(slab[tok], 8);
        assert_eq!(slab.count(), 2);
    }

    #[test]
    fn test_replace_with() {
        let mut slab = Slab::<u32, usize>::new(16);
        let tok = slab.insert(5u32).unwrap();
        assert!(slab.replace_with(tok, |x| Some(x + 1)).is_ok());
        assert!(slab.replace_with(tok + 1, |x| Some(x + 1)).is_err());
        assert_eq!(slab[tok], 6);
    }

    #[test]
    fn test_retain() {
        let mut slab = Slab::<usize, usize>::new(2);
        let tok1 = slab.insert(0).unwrap();
        let tok2 = slab.insert(1).unwrap();
        slab.retain(|x| x % 2 == 0);
        assert_eq!(slab.count(), 1);
        assert_eq!(slab[tok1], 0);
        assert_eq!(slab.contains(tok2), false);
    }

    #[test]
    fn test_iter() {
        let mut slab = Slab::<u32, usize>::new_starting_at(0, 4);
        for i in 0..4 {
            slab.insert(i).unwrap();
        }

        let vals: Vec<u32> = slab.iter().map(|r| *r).collect();
        assert_eq!(vals, vec![0, 1, 2, 3]);

        slab.remove(1);

        let vals: Vec<u32> = slab.iter().map(|r| *r).collect();
        assert_eq!(vals, vec![0, 2, 3]);
    }

    #[test]
    fn test_iter_mut() {
        let mut slab = Slab::<u32, usize>::new_starting_at(0, 4);
        for i in 0..4 {
            slab.insert(i).unwrap();
        }
        for e in slab.iter_mut() {
            *e = *e + 1;
        }

        let vals: Vec<u32> = slab.iter().map(|r| *r).collect();
        assert_eq!(vals, vec![1, 2, 3, 4]);

        slab.remove(2);
        for e in slab.iter_mut() {
            *e = *e + 1;
        }

        let vals: Vec<u32> = slab.iter().map(|r| *r).collect();
        assert_eq!(vals, vec![2, 3, 5]);
    }

    #[test]
    fn test_iter_with_offset() {
        let mut slab = Slab::<u32, usize>::new_starting_at(2, 4);
        for i in 0..4 {
            slab.insert(i).unwrap();
        }

        let vals: Vec<u32> = slab.iter().map(|r| *r).collect();
        assert_eq!(vals, vec![0, 1, 2, 3]);
    }

    #[test]
    fn test_iter_mut_with_offset() {
        let mut slab = Slab::<u32, usize>::new_starting_at(2, 4);
        for i in 0..4 {
            slab.insert(i).unwrap();
        }

        let vals: Vec<u32> = slab.iter_mut().map(|r| *r).collect();
        assert_eq!(vals, vec![0, 1, 2, 3]);
    }

    #[test]
    fn test_grow() {
        let mut slab = Slab::<u32, usize>::new_starting_at(2, 4);
        for i in 0..4 {
            slab.insert(i).unwrap();
        }

        assert!(slab.insert(0).is_err());

        slab.grow(3);

        let vals: Vec<u32> = slab.iter().map(|r| *r).collect();
        assert_eq!(vals, vec![0, 1, 2, 3]);

        for i in 0..3 {
            slab.insert(i).unwrap();
        }
        assert!(slab.insert(0).is_err());

        let vals: Vec<u32> = slab.iter().map(|r| *r).collect();
        assert_eq!(vals, vec![0, 1, 2, 3, 0, 1, 2]);
    }

    #[test]
    fn test_clear() {
        let mut slab = Slab::<u32, usize>::new_starting_at(2, 4);
        for i in 0..4 {
            slab.insert(i).unwrap();
        }

        // clear full
        slab.clear();

        let vals: Vec<u32> = slab.iter().map(|r| *r).collect();
        assert_eq!(vals, vec![]);

        for i in 0..2 {
            slab.insert(i).unwrap();
        }

        let vals: Vec<u32> = slab.iter().map(|r| *r).collect();
        assert_eq!(vals, vec![0, 1]);


        // clear half-filled
        slab.clear();

        let vals: Vec<u32> = slab.iter().map(|r| *r).collect();
        assert_eq!(vals, vec![]);
    }

    #[test]
    fn test_entry() {
        let capacity = 16;
        let offset = 12;
        let mut slab = Slab::<usize, usize>::new_starting_at(offset, capacity);

        // Run through a few times to check clear-fill cycle.
        for _ in 0..3 {
            for i in offset..offset + capacity {
                // Insert values.
                slab.entry(i).unwrap().or_insert(i - offset);
            }

            for i in offset..offset + capacity {
                // Check second or_insert_with doesn't call the closure and
                // returns the existing value.
                assert_eq!(*slab.entry(i).unwrap().or_insert_with(|_| panic!()),
                           i - offset);
            }

            for i in offset..offset + capacity {
                match slab.entry(i).unwrap() {
                    Entry::Occupied(o) => {
                        let (val, vacant) = o.remove();
                        assert_eq!(val, i - offset);

                        // Fill with vacant, remove again.
                        let o = vacant.insert(i * 2);
                        assert_eq!(o.remove().0, i * 2);
                    }
                    Entry::Vacant(_) => panic!("Unexpected vacant entry!"),
                }
            }
        }
    }
}
