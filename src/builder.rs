use crate::{Entry, Slab};

// Building `Slab` from pairs (usize, T).
pub(crate) struct Builder<T> {
    slab: Slab<T>,
    vacant_list_broken: bool,
    first_vacant_index: Option<usize>,
    // `len` is derived from this in `build()`, so pushing in order
    // doesn't have to update a counter for every pair.
    vacant: usize,
}

impl<T> Builder<T> {
    pub(crate) fn with_capacity(capacity: usize) -> Self {
        Self {
            slab: Slab::with_capacity(capacity),
            vacant_list_broken: false,
            first_vacant_index: None,
            vacant: 0,
        }
    }
    pub(crate) fn pair(&mut self, key: usize, value: T) {
        let slab = &mut self.slab;
        if key < slab.entries.len() {
            // iterator is not sorted, might need to recreate vacant list
            if let Entry::Vacant(_) = slab.entries[key] {
                self.vacant_list_broken = true;
                self.vacant -= 1;
            }
            // if an element with this key already exists, replace it.
            // This is consistent with HashMap and BtreeMap
            slab.entries[key] = Entry::Occupied(value);
        } else {
            if self.first_vacant_index.is_none() && slab.entries.len() < key {
                self.first_vacant_index = Some(slab.entries.len());
            }
            // insert holes as necessary
            self.vacant += key - slab.entries.len();
            while slab.entries.len() < key {
                // add the entry to the start of the vacant list
                let next = slab.next;
                slab.next = slab.entries.len();
                slab.entries.push(Entry::Vacant(next));
            }
            slab.entries.push(Entry::Occupied(value));
        }
    }

    pub(crate) fn build(self) -> Slab<T> {
        let mut slab = self.slab;
        slab.len = slab.entries.len() - self.vacant;
        if slab.len == slab.entries.len() {
            // no vacant entries, so next might not have been updated
            slab.next = slab.entries.len();
        } else if self.vacant_list_broken {
            slab.recreate_vacant_list();
        } else if let Some(first_vacant_index) = self.first_vacant_index {
            let next = slab.entries.len();
            match &mut slab.entries[first_vacant_index] {
                Entry::Vacant(n) => *n = next,
                _ => unreachable!(),
            }
        } else {
            unreachable!()
        }
        slab
    }
}
