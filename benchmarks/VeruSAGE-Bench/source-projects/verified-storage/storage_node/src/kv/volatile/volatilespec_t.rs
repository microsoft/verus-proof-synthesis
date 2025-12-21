//! A `VolatileKvIndex` represents the volatile component of a `KvStore`.
//! Currently, it maps each key to 1) the physical offset of the metadata header associated
//! with that key in the header store, and 2) a list of physical offsets of list entries
//! associated with that key.

#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::kv::kvimpl_t::*;
use std::hash::Hash;

verus! {
    pub struct ListNodeIndexEntry {
        pub start_index: int, // first logical list index stored in this node
        pub live_index: int, // first physical slot occupied by a valid list entry
        pub physical_offset: int, // TODO: this can probably be removed?
        pub free_entries: int,
    }

    impl ListNodeIndexEntry {
        pub open spec fn has_free_space(self) -> bool
        {
            self.free_entries > 0
        }

        // Reflects an entry being appended to the corresponding durable list node
        // by updating the number of entries for the node in the index
        pub open spec fn append_entry<K, E>(self) -> Result<Self, KvError<K, E>>
            where
                K: std::fmt::Debug,
                E: std::fmt::Debug,
        {
            if self.free_entries <= 0 {
                Err(KvError::OutOfSpace)
            } else {
                Ok(Self {
                    start_index: self.start_index,
                    live_index: self.live_index,
                    physical_offset: self.physical_offset,
                    free_entries: self.free_entries - 1
                })
            }
        }
    }

    pub struct VolatileKvIndexEntry
    {
        pub item_offset: int, // the physical offset of the metadata header associated with this key
        pub list_node_offsets: Map<(int, int), ListNodeIndexEntry>, // maps a range of indexes to the corresponding entry
        pub list_len: int,
    }

    #[verifier::reject_recursive_types(K)]
    pub struct VolatileKvIndexView<K>
    where
        K: Hash + Eq,
    {
        pub contents: Map<K, VolatileKvIndexEntry>,
        pub list_entries_per_node: int
    }

    impl<K> VolatileKvIndexView<K>
    where
        K: Hash + Eq + std::fmt::Debug,
    {
        pub open spec fn spec_index(&self, key: K) -> Option<VolatileKvIndexEntry>
        {
            if self.contents.contains_key(key) {
                Some(self.contents.index(key))
            } else {
                None
            }
        }

        pub open spec fn contains_key(&self, key: K) -> bool
        {
            self[key] is Some
        }

        pub open spec fn len(&self) -> int
        {
            self.contents.len() as int
        }

        pub open spec fn insert_item_offset(&self, key: K, item_offset: int) -> Self
        {
            Self {
                contents: self.contents.insert(
                        key,
                        VolatileKvIndexEntry {
                            item_offset,
                            list_node_offsets: Map::empty(),
                            list_len: 0
                        }
                    ),
                list_entries_per_node:self.list_entries_per_node
            }
        }

        // adds a new list node's offset to the volatile index. In order to call this, we must have first
        // allocated a new node and inserted an entry into it in the durable store, so we insert
        // the node into the index with `num_entries` set to 1.
        pub open spec fn append_node_offset(&self, key: K, node_offset: int, start_index: int) -> Self
        {
            let current_entry = self.contents[key];
            Self {
                contents: self.contents.insert(
                    key,
                    VolatileKvIndexEntry {
                        item_offset: current_entry.item_offset,
                        list_node_offsets: current_entry.list_node_offsets.insert(
                            (start_index, start_index + 1),
                            ListNodeIndexEntry {
                                start_index,
                                live_index: 0,
                                physical_offset: node_offset,
                                free_entries: self.list_entries_per_node
                            }),
                        list_len: current_entry.list_len + 1
                    }),
                list_entries_per_node: self.list_entries_per_node,
            }
        }


        // Returns the index key and the view of the list node that contains the specified
        // logical list index.
        pub open spec fn get_node_view<E>(&self, key: K, index: int) -> Result<((int, int), ListNodeIndexEntry), KvError<K,E>>
            where
                E: std::fmt::Debug
        {
            if !self.contains_key(key) {
                Err(KvError::KeyNotFound)
            } else {
                let index_entry = self.contents[key];
                if exists |k| {
                    let (i, j) = k;
                    &&& i <= index < j
                    &&& #[trigger] index_entry.list_node_offsets.contains_key(k)
                } {
                    let range = choose |k| {
                        let (i, j) = k;
                        &&& i <= index < j
                        &&& #[trigger] index_entry.list_node_offsets.contains_key(k)
                    };
                    Ok((range, index_entry.list_node_offsets[range]))
                } else {
                    Err(KvError::IndexOutOfRange)
                }
            }
        }

        // returns the offset of the node that contains the specified logical list index
        pub open spec fn get_node_offset<E>(&self, key: K, index: int) -> Result<int, KvError<K, E>>
            where
                E: std::fmt::Debug
        {
            match self.get_node_view(key, index) {
                Ok((_, node_view)) => Ok(node_view.physical_offset),
                Err(e) => Err(e)
            }
        }

        // returns the length of the list associated with this key
        // TODO: should maintain as an invariant that this actually matches the
        // number of entries in all associated nodes
        pub open spec(checked) fn list_len(&self, key: K) -> int
            recommends
                self.contains_key(key)
        {
            self[key].unwrap().list_len
        }

        // Updates the index to reflect that an entry has been appended to the end of the list.
        // It doesn't actually matter what the entry is -- we just need to update the index
        // to reflect that something new has been added
        pub open spec fn append_to_list<E>(self, key: K) -> Result<Self, KvError<K, E>>
            where
                E: std::fmt::Debug
        {
            if !self.contents.contains_key(key) {
                Err(KvError::KeyNotFound)
            } else {
                let old_index_entry = self.contents[key];
                match self.get_node_view(key, old_index_entry.list_len - 1) {
                    Ok((range, old_node_view)) => {
                        let new_node_view = old_node_view.append_entry();
                        match new_node_view {
                            Ok(new_node_view) => {
                                let new_index_entry = VolatileKvIndexEntry {
                                    item_offset: old_index_entry.item_offset,
                                    list_node_offsets: old_index_entry.list_node_offsets.insert(range, new_node_view),
                                    list_len: old_index_entry.list_len + 1
                                };

                                Ok(Self {
                                    contents: self.contents.insert(key, new_index_entry),
                                    list_entries_per_node: self.list_entries_per_node
                                })
                            }
                            Err(e) => Err(e)
                        }
                    }
                    Err(e) => Err(e)
                }
            }

        }

        // TODO: clean this up/split into multiple spec functions
        pub open spec fn trim_list<E>(self, key: K, trim_length: int) -> Result<Self, KvError<K, E>>
            where
                E: std::fmt::Debug
        {
            if !self.contents.contains_key(key) {
                Err(KvError::KeyNotFound)
            } else {
                let entry = self.contents[key];
                // First, determine which (if any) nodes will be completely removed
                let nodes_to_remove = Set::new(|k| {
                    let (i, j) = k;
                    &&& i <= j < trim_length
                    &&& entry.list_node_offsets.contains_key((i, j))
                });
                // There may also be a node that needs some internal trimming
                // let (range_key, node_to_trim_internally) = self.get_node_view(key, trim_length);
                match self.get_node_view(key, trim_length) {
                    Ok((range_key, node_to_trim_internally)) => {
                        let internal_trim_size = trim_length - node_to_trim_internally.start_index;
                        let trimmed_entry = ListNodeIndexEntry {
                            start_index: 0, // this is the new head node
                            live_index: node_to_trim_internally.live_index + internal_trim_size,
                            physical_offset: node_to_trim_internally.physical_offset,
                            free_entries: node_to_trim_internally.free_entries + internal_trim_size,
                        };

                        // Since we have trimmed from the front, we have to rekey all of the remaining
                        // nodes, since their indexes have changed.
                        // TODO: this is fine here, but this could have significant performance issues
                        // if the in-memory index has to do this... so maybe we need to index on something
                        // different? Or use a structure that doesn't depend on keys (e.g. put them in vector)
                        let new_node_map = entry.list_node_offsets
                            .remove_keys(nodes_to_remove) // remove nodes that will be deleted entirely
                            .remove(range_key); // remove the node to trim so that we can update other nodes without worrying about this one

                        // shift all indexes in the map over by the trim length
                        let shifted_node_map = Map::new(
                            |k: (int, int)| {
                                let (i, j) = k;
                                new_node_map.contains_key((i + trim_length, j + trim_length))
                            },
                            |k: (int, int)| {
                                let (i, j) = k;
                                let entry = new_node_map[(i, j)];
                                ListNodeIndexEntry {
                                    start_index: i,
                                    live_index: entry.live_index,
                                    physical_offset: entry.physical_offset,
                                    free_entries: entry.free_entries
                                }
                            }
                        );

                        // add the trimmed node entry back in
                        let final_node_map = shifted_node_map.insert(range_key, trimmed_entry);

                        Ok(Self {
                            contents: self.contents.insert(
                                key,
                                VolatileKvIndexEntry {
                                    item_offset: entry.item_offset,
                                    list_node_offsets: final_node_map,
                                    list_len: entry.list_len - trim_length
                                }
                            ),
                            list_entries_per_node: self.list_entries_per_node
                        })
                    }
                    Err(e) => Err(e)
                }
            }
        }

        pub closed spec fn remove(&self, key: K) -> Self
        {
            Self {
                contents: self.contents.remove(key),
                list_entries_per_node: self.list_entries_per_node
            }
        }

        pub open spec fn empty(self) -> bool {
            &&& self.contents.is_empty()
            &&& self.contents.dom().finite()
        }

        pub open spec fn keys(self) -> Set<K> {
            self.contents.dom()
        }
    }


}
