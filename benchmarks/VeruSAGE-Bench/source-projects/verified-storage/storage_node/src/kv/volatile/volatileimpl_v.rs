//! This file contains a trait that defines the interface for the high-level
//! volatile component of the KV store.

#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::kv::kvimpl_t::*;
use crate::kv::volatile::volatilespec_t::*;
use crate::pmem::pmcopy_t::*;
use std::hash::Hash;

verus! {
    pub trait VolatileKvIndex<K, E> : Sized
    where
        K: Hash + Eq + Clone + PmCopy + Sized + std::fmt::Debug,
        E: std::fmt::Debug,
    {
        spec fn view(&self) -> VolatileKvIndexView<K>;

        spec fn valid(&self) -> bool;

        fn new(
            kvstore_id: u128,
            max_keys: usize,
        ) -> (result: Result<Self, KvError<K, E>>)
            ensures
                match result {
                    Ok(volatile_index) => {
                        &&& volatile_index@.empty()
                        &&& volatile_index.valid()
                    }
                    Err(_) => true // TODO
                }
        ;

        fn insert_item_offset(
            &mut self,
            key: &K,
            offset: u64,
        ) -> (result: Result<(), KvError<K, E>>)
            requires
                old(self).valid(),
                old(self)@[*key] is None,
            ensures
                self.valid(),
                match result {
                    Ok(()) => {
                        &&& self@ == old(self)@.insert_item_offset(*key, offset as int)
                        &&& self@.len() == old(self)@.len() + 1
                    }
                    Err(_) => false // TODO
                }
        ;

        fn append_to_list(
            &mut self,
            key: &K,
        ) -> (result: Result<(), KvError<K, E>>)
            requires
                old(self).valid(),
                // The caller has to prove that 1) the key exists and 2) the node we will add to has free
                // space. This function should be called only after a successful durable append,
                // which they can use to prove this.
                old(self)@.contains_key(*key),
                ({
                    let (_, node_view) = old(self)@.get_node_view::<E>(*key, old(self)@.list_len(*key) - 1).unwrap();
                    node_view.has_free_space()
                })
            ensures
                self.valid(),
                ({
                    let spec_result = old(self)@.append_to_list::<E>(*key);
                    match (result, spec_result) {
                        (Ok(()), Ok(new_state)) => self@ == new_state,
                        (Ok(()), Err(_)) => false,
                        (Err(KvError::KeyNotFound), Err(KvError::KeyNotFound)) => {
                            &&& !old(self)@.contains_key(*key)
                            &&& self@ == old(self)@
                        }
                        _ => false
                    }
                })
        ;

        fn get(
            &self,
            key: &K
        ) -> (result: Option<u64>)
            requires
                self.valid(),
            ensures
                match result {
                    Some(offset) => match self@[*key] {
                            Some(val) => offset == val.item_offset,
                            None => false
                        }
                    None => self@[*key].is_None()
                }
        ;

        // Returns the physical location of the list entry at the specified index.
        // Returns the address of the entry, not the address of the node that contains it
        fn get_entry_location_by_index(
            &self,
            key: &K,
            idx: usize,
        ) -> (result: Result<u64, KvError<K, E>>)
            requires
                self.valid(),
            ensures
                match result {
                    Ok(offset) => match self@[*key] {
                        Some(entry) => true, // TODO
                        // Some(entry) => entry.list_node_offsets[idx as int] == offset as int,
                        None => false
                    },
                    Err(KvError::KeyNotFound) => !self@.contains_key(*key),
                    Err(KvError::IndexOutOfRange) => match self@[*key] {
                        Some(entry) => idx >= entry.list_node_offsets.len(),
                        None => false
                    }
                    Err(_) => false,
                }
        ;

        // returns a pointer to the list node that contains the specified index
        fn get_node_offset(
            &self,
            key: &K,
            idx: usize
        ) -> (result: Result<u64, KvError<K, E>>)
            requires
                self.valid(),
            ensures
                ({
                    let spec_result = self@.get_node_offset::<E>(*key, idx as int);
                    match (result, spec_result) {
                        (Ok(node_offset), Ok(spec_offset)) => node_offset as int == spec_offset,
                        (Err(KvError::KeyNotFound), Err(KvError::KeyNotFound)) => !self@.contains_key(*key),
                        (Err(KvError::IndexOutOfRange), Err(KvError::IndexOutOfRange)) => idx >= self@[*key].unwrap().list_len,
                        _ => false
                    }
                })
        ;

        fn remove(
            &mut self,
            key: &K
        ) -> (result: Result<u64, KvError<K, E>>)
            requires
                old(self).valid(),
            ensures
                self.valid(),
                match result {
                    Ok(offset) => {
                        match old(self)@[*key] {
                            Some(entry) => {
                                &&& entry.item_offset == offset as int
                                &&& self@[*key].is_None()
                            }
                            None => false
                        }
                    }
                    Err(_) => true // TODO
                }
        ;

        // trims the volatile index for the list associated with the key
        fn trim_list(
            &mut self,
            key: &K,
            trim_length: usize
        ) -> (result: Result<(), KvError<K, E>>)
            requires
                old(self).valid(),
            ensures
                self.valid(),
                ({
                    let spec_result = old(self)@.trim_list::<E>(*key, trim_length as int);
                    match (result, spec_result) {
                        (Ok(()), Ok(spec_self)) => self@ == spec_self,
                        (Err(KvError::KeyNotFound), Err(KvError::KeyNotFound)) => {
                            &&& !old(self)@.contains_key(*key)
                            &&& self@ == old(self)@
                        }
                        (Err(KvError::IndexOutOfRange), Err(KvError::IndexOutOfRange)) => {
                            &&& old(self)@.contains_key(*key)
                            &&& old(self)@[*key].unwrap().list_len <= trim_length
                            &&& self@ == old(self)@
                        }
                        _ => false
                    }
                })
        ;

        fn get_keys(
            &self
        ) -> (result: Vec<K>)
            requires
                self.valid(),
            ensures
                self@.keys() == result@.to_set()
        ;

    }
}
