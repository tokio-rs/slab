use core::mem::replace;

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
            match replace(&mut slab.entries.as_mut()[index], Entry::Unknown) {
                Entry::Vacant { .. } => {
                    self.vacant_list_broken = true;
                    slab.meta.len += 1;
                }
                Entry::Occupied {
                    #[cfg(feature = "range")]
                    range,
                    ..
                } => {
                    #[cfg(feature = "range")]
                    slab.remove_occupied_index(index, range);
                }
                _ => unreachable!(),
            }

            #[cfg(feature = "range")]
            let range = slab.insert_occupied_index(index);

            // if an element with this key already exists, replace it.
            // This is consistent with HashMap and BtreeMap
            slab.entries.as_mut()[index] = Entry::Occupied {
                value,
                key_data: key.into_occupied_data(),
                #[cfg(feature = "range")]
                range,
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

            #[cfg(feature = "range")]
            let range = slab.insert_occupied_index(index);

            slab.entries.push(Entry::Occupied {
                value,
                key_data: key.into_occupied_data(),
                #[cfg(feature = "range")]
                range,
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
