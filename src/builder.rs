use crate::entries::{Entries, Entry};
use crate::generic::GenericSlab;
use crate::key::Key;

// Building `Slab` from pairs (usize, T).
pub(crate) struct Builder<T, TKey, TEntries>
where
    TKey: Key<T>,
{
    slab: GenericSlab<T, TKey, TEntries>,
    vacant_list_broken: bool,
    first_vacant_index: Option<usize>,
}

impl<T, TKey, TEntries> Builder<T, TKey, TEntries>
where
    TKey: Key<T>,
    TEntries: Entries<T, TKey> + Default,
{
    pub(crate) fn new() -> Self {
        Self {
            slab: GenericSlab::default(),
            vacant_list_broken: false,
            first_vacant_index: None,
        }
    }
    pub(crate) fn pair(&mut self, key: TKey, value: T) {
        let index = key.index(&self.slab.meta.key_context);
        let slab = &mut self.slab;

        if index < slab.entries.as_ref().len() {
            let entry = &mut slab.entries.as_mut()[index];

            // iterator is not sorted, might need to recreate vacant list
            if let Entry::Vacant { .. } = &*entry {
                self.vacant_list_broken = true;
                slab.meta.len += 1;
            }

            // if an element with this key already exists, replace it.
            // This is consistent with HashMap and BtreeMap
            *entry = Entry::Occupied {
                value,
                key_data: Default::default(),
            };
        } else {
            if self.first_vacant_index.is_none() && slab.entries.as_ref().len() < index {
                self.first_vacant_index = Some(slab.entries.as_ref().len());
            }

            // insert holes as necessary
            while slab.entries.as_ref().len() < index {
                // add the entry to the start of the vacant list
                let next = slab.meta.first_vacant;
                slab.meta.first_vacant = slab.entries.as_ref().len();
                slab.entries.push(Entry::Vacant {
                    next,
                    key_data: Default::default(),
                });
            }
            slab.entries.push(Entry::Occupied {
                value,
                key_data: Default::default(),
            });
            slab.meta.len += 1;
        }
    }

    pub(crate) fn build(self) -> GenericSlab<T, TKey, TEntries> {
        let mut slab = self.slab;

        if slab.meta.len == slab.entries.as_ref().len() {
            // no vacant entries, so next might not have been updated
            slab.meta.first_vacant = slab.entries.as_ref().len();
        } else if self.vacant_list_broken {
            slab.recreate_vacant_list();
        } else if let Some(first_vacant_index) = self.first_vacant_index {
            let next = slab.entries.as_ref().len();
            match &mut slab.entries.as_mut()[first_vacant_index] {
                Entry::Vacant { next: n, .. } => *n = next,
                _ => unreachable!(),
            }
        } else {
            unreachable!()
        }

        slab
    }
}
