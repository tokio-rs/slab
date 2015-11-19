use std::{fmt, mem, usize};
use std::iter::IntoIterator;
use std::ops;
use std::marker::PhantomData;

/// A preallocated chunk of memory for storing objects of the same type.
pub struct Slab<T, I: Index> {
    // Chunk of memory
    entries: Vec<Entry<T>>,

    // Number of Filled elements currently in the slab
    len: usize,

    // The index offset
    offset: usize,

    // Offset of the next available slot in the slab. Set to the slab's
    // capacity when the slab is full.
    next: usize,

    _marker: PhantomData<I>,
}

enum Entry<T> {
    Empty(usize),
    Filled(T),
}

// Need this for Rust 1.0 compatibility
// See: https://github.com/rust-lang/rust/issues/15609
impl<T> Entry<T> {
    #[inline]
    fn as_mut(&mut self) -> Option<&mut T> {
        match *self {
            Entry::Filled(ref mut val) => Some(val),
            Entry::Empty(_) => None,
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

unsafe impl<T, I : Index> Send for Slab<T, I> where T: Send {}

macro_rules! some {
    ($expr:expr) => (match $expr {
        Some(val) => val,
        None => return None,
    })
}

impl<T, I: Index> Slab<T, I> {
    pub fn new(capacity: usize) -> Slab<T, I> {
        Slab::new_starting_at(I::from_usize(0), capacity)
    }

    pub fn new_starting_at(offset: I, capacity: usize) -> Slab<T, I> {
        assert!(capacity <= usize::MAX, "capacity too large");
        let entries = (1..capacity+1)
            .map(Entry::Empty)
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
        match self.get(idx) {
            Some(_) => true,
            None => false
        }
    }

    pub fn get(&self, idx: I) -> Option<&T> {
        let idx = some!(self.local_index(idx));

        match self.entries[idx] {
            Entry::Filled(ref val) => Some(val),
            Entry::Empty(_) => None,
        }
    }

    pub fn get_mut(&mut self, idx: I) -> Option<&mut T> {
        let idx = some!(self.local_index(idx));

        return self.entries[idx].as_mut();
    }

    pub fn insert(&mut self, val: T) -> Result<I, T> {
        // check fail condition before val gets moved by insert_with,
        // so `Err(val)` can be returned
        if self.next >= self.entries.len() {
            return Err(val);
        }

        match self.insert_with(move |_| val ) {
            None => panic!("Slab::insert_with() should have not failed"),
            Some(idx) => Ok(idx)
        }
    }

    /// Like `insert` but for objects that require newly allocated
    /// usize in their constructor.
    pub fn insert_with<F>(&mut self, fun: F) -> Option<I> where F : FnOnce(I) -> T {
        let idx = self.next;
        if idx >= self.entries.len() {
            return None;
        }

        self.next = match self.entries[idx] {
            Entry::Empty(next) => next,
            Entry::Filled(_) => panic!("Tried to insert into filled index")
        };

        self.entries[idx] = Entry::Filled(fun(I::from_usize(idx + self.offset)));
        self.len += 1;
        Some(I::from_usize(idx + self.offset))
    }

    /// Releases the given slot
    pub fn remove(&mut self, idx: I) -> Option<T> {
        let next = self.next;
        self.replace_(idx, Entry::Empty(next))
    }

    pub fn replace(&mut self, idx: I, t : T) -> Option<T> {
        self.replace_(idx, Entry::Filled(t))
    }

    /// Execute a function on the *value* in the slot and put the result of
    /// the function back into the slot. If function returns None,
    /// slot is left empty on exit.
    ///
    /// Returns Err(()) if slot was empty
    ///
    /// This method is very useful for storing state machines inside Slab
    pub fn replace_with<F>(&mut self, idx: I, fun: F) -> Result<(), ()>
        where F: FnOnce(T) -> Option<T> {

            let raw_idx = idx.as_usize();

            // In current implementation we can just remove the element and insert
            // it again, but this guarantee is not documented
            if let Some(val) = self.remove(idx) {
                match fun(val) {
                    Some(newval) => {
                        let new_idx = self.insert(newval).ok().expect("We just deleted");
                        // ... so we just assert that this guarantee is still ok
                        debug_assert!(raw_idx == new_idx.as_usize());
                        Ok(())
                    },
                    None => Ok(())
                }
            } else {
                Err(())
            }
        }

    /// Retain only the elements specified by the predicate.
    ///
    /// In other words, remove all elements `e` such that `f(&e)` returns false.
    /// This method operates in place and preserves the order of the retained
    /// elements.
    pub fn retain<F>(&mut self, mut fun: F) where F: FnMut(&T) -> bool {
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

    pub fn iter(&self) -> SlabIter<T, I> {
        SlabIter {
            slab: self,
            cur_idx: 0,
            yielded: 0
        }
    }

    pub fn iter_mut(&mut self) -> SlabMutIter<T, I> {
        SlabMutIter { iter: self.iter() }
    }

    /// Empty the slab, by freeing all entries
    pub fn clear(&mut self) {
        for (i, e) in self.entries.iter_mut().enumerate() {
            *e = Entry::Empty(i + 1)
        }
        self.next = 0;
        self.len = 0;
    }

    /// Grow the slab, by adding `entries_num`
    pub fn grow(&mut self, entries_num : usize) {
        let prev_len = self.entries.len();
        let prev_len_next = prev_len + 1;
        self.entries.extend(
            (prev_len_next..(prev_len_next + entries_num))
            .map(|n| Entry::Empty(n))
            );
        debug_assert_eq!(self.entries.len(), prev_len + entries_num);
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
    fn replace_(&mut self, idx: I, e: Entry<T>) -> Option<T> {
        let idx = some!(self.local_index(idx));

        if let Entry::Filled(val) = mem::replace(&mut self.entries[idx], e) {
            self.next = idx;
            self.len -= 1;
            return Some(val);
        }

        None
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

impl<T, I : Index> fmt::Debug for Slab<T, I> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "Slab {{ len: {}, cap: {} }}", self.len, self.entries.len())
    }
}

pub struct SlabIter<'a, T: 'a, I : Index+'a> {
    slab: &'a Slab<T, I>,
    cur_idx: usize,
    yielded: usize
}

impl<'a, T, I : Index> Iterator for SlabIter<'a, T, I> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        while self.yielded < self.slab.len {
            match self.slab.entries[self.cur_idx] {
                Entry::Filled(ref v) => {
                    self.cur_idx += 1;
                    self.yielded += 1;
                    return Some(v);
                }
                Entry::Empty(_) => {
                    self.cur_idx += 1;
                }
            }
        }

        None
    }
}

pub struct SlabMutIter<'a, T: 'a, I : Index+'a> {
    iter: SlabIter<'a, T, I>,
}

impl<'a, T, I : Index> Iterator for SlabMutIter<'a, T, I> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<&'a mut T> {
        unsafe { mem::transmute(self.iter.next()) }
    }
}

impl<'a, T, I : Index> IntoIterator for &'a Slab<T, I> {
    type Item = &'a T;
    type IntoIter = SlabIter<'a, T, I>;

    fn into_iter(self) -> SlabIter<'a, T, I> {
        self.iter()
    }
}

impl<'a, T, I : Index> IntoIterator for &'a mut Slab<T, I> {
    type Item = &'a mut T;
    type IntoIter = SlabMutIter<'a, T, I>;

    fn into_iter(self) -> SlabMutIter<'a, T, I> {
        self.iter_mut()
    }
}

#[cfg(test)]
mod tests {
    use super::Slab;

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
        let mut slab = Slab::new_starting_at(5 ,16);
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
        assert!(slab.replace(tok+1, 555).is_none());
        assert_eq!(slab[tok], 6);
    }

    #[test]
    fn test_replace_with() {
        let mut slab = Slab::<u32, usize>::new(16);
        let tok = slab.insert(5u32).unwrap();
        assert!(slab.replace_with(tok, |x| Some(x+1)).is_ok());
        assert!(slab.replace_with(tok+1, |x| Some(x+1)).is_err());
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

}
