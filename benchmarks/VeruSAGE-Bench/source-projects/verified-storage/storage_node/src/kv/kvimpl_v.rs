//! This file contains the verified implementation of the KV store. The methods
//! defined here are meant to be called by methods in kvimpl_t.rs with `Perm`
//! arguments that have been audited along with the rest of that file.
//!
//! The UntrustedKvStoreImpl is split into two key components: a volatile index
//! and a durable store. Each of these may be further split into separate components,
//! but having a high-level split between volatile and durable should make the
//! distinction between updates that require crash-consistency proofs, and updates
//! that don't, clear. The view of an UntrustedKvStoreImpl is obtained using the contents
//! of its current volatile and durable components.

#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::seq::*;

use super::durable::durableimpl_v::*;
use super::durable::durablespec_t::*;
use super::inv_v::*;
use super::kvspec_t::*;
use super::volatile::volatileimpl_v::*;
use super::volatile::volatilespec_t::*;
use crate::kv::kvimpl_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;

use std::hash::Hash;

verus! {

pub struct UntrustedKvStoreImpl<PM, K, I, L, D, V, E>
where
    PM: PersistentMemoryRegions,
    K: Hash + Eq + Clone + PmCopy + std::fmt::Debug,
    I: PmCopy + Item<K> + std::fmt::Debug,
    L: PmCopy + std::fmt::Debug,
    D: DurableKvStore<PM, K, I, L, E>,
    V: VolatileKvIndex<K, E>,
    E: std::fmt::Debug,
{
    id: u128,
    durable_store: D,
    volatile_index: V,
    entries_per_list_node: usize,
    _phantom: Ghost<core::marker::PhantomData<(PM, K, I, L, E)>>,
}

impl<PM, K, I, L, D, V, E> UntrustedKvStoreImpl<PM, K, I, L, D, V, E>
where
    PM: PersistentMemoryRegions,
    K: Hash + Eq + Clone + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Item<K> + Sized + std::fmt::Debug,
    L: PmCopy + std::fmt::Debug,
    D: DurableKvStore<PM, K, I, L, E>,
    V: VolatileKvIndex<K, E>,
    E: std::fmt::Debug,
{

    // This function specifies how all durable contents of the KV
    // should be viewed upon recovery as an abstract paged KV state.
    // TODO: write this
    pub closed spec fn recover(mems: Seq<Seq<u8>>, kv_id: u128) -> Option<AbstractKvStoreState<K, I, L, E>>
    {
        None
    }

    pub closed spec fn view(&self) -> AbstractKvStoreState<K, I, L, E>
    {
        AbstractKvStoreState {
            id: self.id,
            contents: AbstractKvStoreState::construct_view_contents(
                self.volatile_index@, self.durable_store@),
            _phantom: None,
        }
    }

    // Proves that if the durable store and volatile index comprising a KV are both empty,
    // then the view of the KV is also empty.
    proof fn lemma_empty_kv(self)
        requires
            self.durable_store@.empty(),
            self.volatile_index@.empty(),
        ensures
            self@.empty()
    {
        lemma_empty_map_contains_no_keys(self.volatile_index@.contents);
        assert(Set::new(|k| self.volatile_index@.contains_key(k)) =~= Set::<K>::empty());
    }

    pub closed spec fn valid(self) -> bool
    {
        &&& self.durable_store@.matches_volatile_index(self.volatile_index@)
        &&& self.durable_store.valid()
        &&& self.volatile_index.valid()
    }

    pub fn untrusted_new(
        pmem: PM,
        kvstore_id: u128,
        max_keys: usize,
        list_node_size: usize,
    ) -> (result: Result<Self, KvError<K, E>>)
        ensures
            match result {
                Ok(new_kv) => {
                    &&& new_kv.valid()
                }
                Err(_) => true
            }
    {
        let durable_store = D::new(pmem, kvstore_id, max_keys, list_node_size)?;
        let volatile_index = V::new(kvstore_id, max_keys)?;
        let kv = Self {
            id: kvstore_id,
            durable_store,
            volatile_index,
            entries_per_list_node: list_node_size,
            _phantom: Ghost(spec_phantom_data()),
        };
        proof {
            lemma_empty_index_matches_empty_store(durable_store@, volatile_index@);
            kv.lemma_empty_kv();
        }
        Ok(kv)
    }

    pub fn untrusted_create(
        &mut self,
        key: &K,
        item: I,
        perm: Tracked<&TrustedKvPermission<PM, K, I, L, D, E>>
    ) -> (result: Result<(), KvError<K, E>>)
        requires
            old(self).valid(),
            key == item.spec_key(),
        ensures
            self.valid(),
            match result {
                Ok(()) => {
                    &&& self@ == old(self)@.create(*key, item).unwrap()
                }
                Err(KvError::KeyAlreadyExists) => {
                    &&& old(self)@.contents.contains_key(*key)
                    &&& old(self)@ == self@
                }
                Err(_) => false
            }
    {
        // check whether the key already exists
        if self.volatile_index.get(key).is_some() {
            return Err(KvError::KeyAlreadyExists);
        }

        let ghost old_durable_state = self.durable_store@;
        let ghost old_volatile_state = self.volatile_index@;
        let ghost old_kv_state = self@;

        // `item` stores its own key, so we don't have to pass its key to the durable
        // store separately.
        let offset = self.durable_store.create(item, perm)?;
        self.volatile_index.insert_item_offset(key, offset)?;

        proof {
            // the volatile index and durable store match after creating the new entry in both
            lemma_volatile_matches_durable_after_create(old_durable_state, old_volatile_state, offset as int, *key, item);
            let new_kv_state = old_kv_state.create(*key, item).unwrap();
            // the kv state reflects the new volatile and durable store states
            assert(new_kv_state.contents =~= AbstractKvStoreState::construct_view_contents(
                    self.volatile_index@, self.durable_store@));
        }

        Ok(())
    }

    pub fn untrusted_read_item(&self, key: &K) -> (result: Option<&I>)
        requires
            self.valid()
        ensures
        ({
            let spec_result = self@.read_item_and_list(*key);
            match (result, spec_result) {
                (Some(output_item), Some((spec_item, pages))) => {
                    &&& spec_item == output_item
                }
                (Some(output_item), None) => false,
                (None, Some((spec_item, pages))) => false,
                (None, None) => true,
            }
        })
    {
        assume(false); // TODO

        // First, get the offset of the header in the durable store using the volatile index
        let offset = self.volatile_index.get(key);
        match offset {
            Some(offset) => self.durable_store.read_item(offset),
            None => None
        }
    }

    // // TODO: return a Vec<&L> to save space/reduce copies
    // pub fn untrusted_read_item_and_list(&self, key: &K) -> (result: Option<(&I, Vec<&L>)>)
    //     requires
    //         self.valid(),
    //     ensures
    //     ({
    //         let spec_result = self@.read_item_and_list(*key);
    //         match (result, spec_result) {
    //             (Some((output_item, output_pages)), Some((spec_item, spec_pages))) => {
    //                 &&& spec_item == output_item
    //                 &&& spec_pages == output_pages@
    //             }
    //             (Some((output_item, output_pages)), None) => false,
    //             (None, Some((spec_item, spec_pages))) => false,
    //             (None, None) => true,
    //         }
    //     })
    // {
    //     assume(false);
    //     // First, get the offset of the header in the durable store using the volatile index
    //     let offset = self.volatile_index.get(key);
    //     match offset {
    //         Some(offset) => self.durable_store.read_item_and_list(offset),
    //         None => None
    //     }
    // }

    pub fn untrusted_read_list_entry_at_index(&self, key: &K, idx: u64) -> (result: Result<&L, KvError<K, E>>)
        requires
            self.valid()
        ensures
            ({
                let spec_result = self@.read_list_entry_at_index(*key, idx as int);
                match (result, spec_result) {
                    (Ok(output_entry), Ok(spec_entry)) => {
                        &&& output_entry == spec_entry
                    }
                    (Err(KvError::IndexOutOfRange), Err(KvError::IndexOutOfRange)) => {
                        &&& self@.contents.contains_key(*key)
                        &&& self@.contents[*key].1.len() <= idx
                    }
                    (Err(KvError::KeyNotFound), Err(KvError::KeyNotFound)) => {
                        &&& !self@.contents.contains_key(*key)
                    }
                    (_, _) => false
                }
            })
    {
        assume(false);
        Err(KvError::NotImplemented)
    }

    // pub fn untrusted_read_list(&self, key: &K) -> (result: Option<&Vec<L>>)
    //     requires
    //         self.valid(),
    //     ensures
    //     ({
    //         let spec_result = self@.read_item_and_list(*key);
    //         match (result, spec_result) {
    //             (Some(output_pages), Some((spec_item, spec_pages))) => {
    //                 &&& spec_pages == output_pages@
    //             }
    //             (Some(output_pages), None) => false,
    //             (None, Some((spec_item, spec_pages))) => false,
    //             (None, None) => true,
    //         }
    //     })
    // {
    //     assume(false);
    //     let offset = self.volatile_index.get(key);
    //     match offset {
    //         Some(offset) => self.durable_store.read_list(offset),
    //         None => None
    //     }
    // }

    pub fn untrusted_update_item(
        &mut self,
        key: &K,
        new_item: I,
        perm: Tracked<&TrustedKvPermission<PM, K, I, L, D, E>>
    ) -> (result: Result<(), KvError<K, E>>)
        requires
            old(self).valid(),
        ensures
            self.valid(),
            match result {
                Ok(()) => {
                    &&& self@ == old(self)@.update_item(*key, new_item).unwrap()
                }
                Err(KvError::KeyNotFound) => {
                    &&& !old(self)@.contents.contains_key(*key)
                    &&& old(self)@ == self@
                }
                Err(_) => false
            }
    {
        assume(false);
        let offset = self.volatile_index.get(key);
        match offset {
            Some(offset) => self.durable_store.update_item(offset, new_item),
            None => Err(KvError::KeyNotFound)
        }
    }

    pub fn untrusted_delete(
        &mut self,
        key: &K,
        perm: Tracked<&TrustedKvPermission<PM, K, I, L, D, E>>
    ) -> (result: Result<(), KvError<K, E>>)
        requires
            old(self).valid()
        ensures
            self.valid(),
            match result {
                Ok(()) => {
                    &&& self@ == old(self)@.delete(*key).unwrap()
                }
                Err(KvError::KeyNotFound) => {
                    &&& !old(self)@.contents.contains_key(*key)
                    &&& old(self)@ == self@
                }
                Err(_) => false
            }
    {
        assume(false);
        // Remove the entry from the volatile index, obtaining the physical offset as the return value
        let offset = self.volatile_index.remove(key)?;
        self.durable_store.delete(offset, perm)
    }

    pub fn untrusted_append_to_list(
        &mut self,
        key: &K,
        new_list_entry: L,
        perm: Tracked<&TrustedKvPermission<PM, K, I, L, D, E>>
    ) -> (result: Result<(), KvError<K, E>>)
        requires
            old(self).valid()
        ensures
            self.valid(),
            match result {
                Ok(()) => {
                    &&& self@ == old(self)@.append_to_list(*key, new_list_entry).unwrap()
                }
                Err(KvError::KeyNotFound) => {
                    &&& !old(self)@.contents.contains_key(*key)
                    &&& old(self)@ == self@
                }
                // TODO: case for if we run out of space to append to the list
                Err(_) => false
            }
    {
        assume(false);
        return Err(KvError::InternalError);
        // let offset = self.volatile_index.get(key);
        // // append a page to the list rooted at this offset
        // let page_offset = match offset {
        //     Some(offset) => self.durable_store.append(offset, new_list_entry, perm)?,
        //     None => return Err(KvError::KeyNotFound)
        // };
        // // add the durable location of the page to the in-memory list
        // self.volatile_index.append_offset_to_list(key, page_offset)
    }

    pub fn untrusted_append_to_list_and_update_item(
        &mut self,
        key: &K,
        new_list_entry: L,
        new_item: I,
        perm: Tracked<&TrustedKvPermission<PM, K, I, L, D, E>>
    ) -> (result: Result<(), KvError<K, E>>)
        requires
            old(self).valid()
        ensures
            self.valid(),
            match result {
                Ok(()) => {
                    &&& self@ == old(self)@.append_to_list_and_update_item(*key, new_list_entry, new_item).unwrap()
                }
                Err(KvError::KeyNotFound) => {
                    &&& !old(self)@.contents.contains_key(*key)
                    &&& old(self)@ == self@
                }
                // TODO: case for if we run out of space to append to the list
                Err(_) => false
            }
    {
        assume(false);
        let offset = self.volatile_index.get(key);
        // update the header at this offset append a page to the list rooted there
        let page_offset = match offset {
            Some(offset) => self.durable_store.update_item_and_append(offset, new_list_entry, new_item, perm)?,
            None => return Err(KvError::KeyNotFound)
        };

        // TODO: use append_node_offset or append_to_list depending on whether you need to allocate or not?
        self.volatile_index.append_to_list(key)
    }

    pub fn untrusted_update_list_entry_at_index(
        &mut self,
        key: &K,
        idx: usize,
        new_list_entry: L,
        perm: Tracked<&TrustedKvPermission<PM, K, I, L, D, E>>
    ) -> (result: Result<(), KvError<K, E>>)
        requires
            old(self).valid()
        ensures
            self.valid(),
            match result {
                Ok(()) => {
                    &&& self@ == old(self)@.update_list_entry_at_index(*key, idx, new_list_entry).unwrap()
                }
                Err(KvError::KeyNotFound) => {
                    &&& !old(self)@.contents.contains_key(*key)
                    &&& old(self)@ == self@
                }
                Err(_) => false
            }
    {
        assume(false);
        let header_offset = self.volatile_index.get(key);
        let entry_offset = self.volatile_index.get_entry_location_by_index(key, idx);
        match (header_offset, entry_offset) {
            (Some(header_offset), Ok(entry_offset)) => self.durable_store.update_list_entry_at_index(header_offset, entry_offset, new_list_entry, perm),
            (None, _) => Err(KvError::KeyNotFound),
            (_, Err(KvError::IndexOutOfRange)) => Err(KvError::IndexOutOfRange),
            (_, Err(_)) => Err(KvError::InternalError), // TODO: better error handling for all cases
        }
    }

    pub fn untrusted_update_entry_at_index_and_item(
        &mut self,
        key: &K,
        idx: usize,
        new_list_entry: L,
        new_item: I,
        perm: Tracked<&TrustedKvPermission<PM, K, I, L, D, E>>
    ) -> (result: Result<(), KvError<K, E>>)
        requires
            old(self).valid()
        ensures
            match result {
                Ok(()) => {
                    &&& self.valid()
                    &&& self@ == old(self)@.update_entry_at_index_and_item(*key, idx, new_list_entry, new_item).unwrap()
                }
                Err(KvError::KeyNotFound) => {
                    &&& !old(self)@.contents.contains_key(*key)
                    &&& old(self)@ == self@
                }
                Err(_) => false
            }
    {
        assume(false);
        let header_offset = self.volatile_index.get(key);
        let entry_offset = self.volatile_index.get_entry_location_by_index(key, idx);
        match (header_offset, entry_offset) {
            (Some(header_offset), Ok(entry_offset)) => self.durable_store.update_entry_at_index_and_item(header_offset, entry_offset, new_item, new_list_entry,  perm),
            (None, _) => Err(KvError::KeyNotFound),
            (_, Err(KvError::IndexOutOfRange)) => Err(KvError::IndexOutOfRange),
            (_, Err(_)) => Err(KvError::InternalError), // TODO: better error handling for all cases
        }
    }

    pub fn untrusted_trim_list(
        &mut self,
        key: &K,
        trim_length: usize,
        perm: Tracked<&TrustedKvPermission<PM, K, I, L, D, E>>
    ) -> (result: Result<(), KvError<K, E>>)
        requires
            old(self).valid()
        ensures
            match result {
                Ok(()) => {
                    &&& self.valid()
                    &&& self@ == old(self)@.trim_list(*key, trim_length as int).unwrap()
                }
                Err(KvError::KeyNotFound) => {
                    &&& !old(self)@.contents.contains_key(*key)
                    &&& old(self)@ == self@
                }
                Err(_) => false
            }
        {
        // use the volatile index to figure out which physical offsets should be removed
        // from the list, then use that information to trim the list on the durable side
        // TODO: trim_length is in terms of list entries, not bytes, right? Check Jay's impl
        // note: we trim from the beginning of the list, not the end
        assume(false);
        let item_offset = self.volatile_index.get(key);
        let old_list_head_offset = self.volatile_index.get_node_offset(key, 0);
        let new_list_head_offset = self.volatile_index.get_node_offset(key, trim_length);
        self.volatile_index.trim_list(key, trim_length)?;
        match (item_offset, old_list_head_offset, new_list_head_offset) {
            (Some(item_offset), Ok(old_list_head_offset), Ok(new_list_head_offset)) =>
                self.durable_store.trim_list(item_offset, old_list_head_offset, new_list_head_offset, trim_length, perm),
            (None, _, _) => Err(KvError::KeyNotFound),
            (_, _, Err(KvError::IndexOutOfRange)) | (_, Err(KvError::IndexOutOfRange), _) => Err(KvError::IndexOutOfRange),
            (_, _, Err(_)) | (_, Err(_), _) => Err(KvError::InternalError), // TODO: better error handling for all cases
        }
    }

    pub fn untrusted_trim_list_and_update_item(
        &mut self,
        key: &K,
        trim_length: usize,
        new_item: I,
        perm: Tracked<&TrustedKvPermission<PM, K, I, L, D, E>>
    ) -> (result: Result<(), KvError<K, E>>)
        requires
            old(self).valid()
        ensures
            match result {
                Ok(()) => {
                    &&& self.valid()
                    &&& self@ == old(self)@.trim_list_and_update_item(*key, trim_length as int, new_item).unwrap()
                }
                Err(KvError::KeyNotFound) => {
                    &&& !old(self)@.contents.contains_key(*key)
                    &&& old(self)@ == self@
                }
                Err(_) => false
            }
    {
        assume(false);
        let item_offset = self.volatile_index.get(key);
        let old_list_head_offset = self.volatile_index.get_node_offset(key, 0);
        let new_list_head_offset = self.volatile_index.get_node_offset(key, trim_length);
        self.volatile_index.trim_list(key, trim_length)?;
        match (item_offset, old_list_head_offset, new_list_head_offset) {
            (Some(item_offset), Ok(old_list_head_offset), Ok(new_list_head_offset)) =>
                self.durable_store.trim_list_and_update_item(item_offset, old_list_head_offset, new_list_head_offset, trim_length, new_item, perm),
            (None, _, _) => Err(KvError::KeyNotFound),
            (_, _, Err(KvError::IndexOutOfRange)) | (_, Err(KvError::IndexOutOfRange), _,) => Err(KvError::IndexOutOfRange),
            (_, _, Err(_)) | (_, Err(_), _)=> Err(KvError::InternalError), // TODO: better error handling for all cases
        }
    }

    pub fn untrusted_get_keys(&self) -> (result: Vec<K>)
        requires
            self.valid()
        ensures
            result@.to_set() == self@.get_keys()
    {
        assume(false);
        self.volatile_index.get_keys()
    }

    pub fn untrusted_contains_key(&self, key: &K) -> (result: bool)
        requires
            self.valid(),
        ensures
            match result {
                true => self@[*key] is Some,
                false => self@[*key] is None
            }
    {
        assume(false);
        self.volatile_index.get(key).is_some()
    }

}

}
