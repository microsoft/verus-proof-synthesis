//! This file contains the public interface of the paged key-value store.
//! The methods offered by this file should match the mocks.
//! The key-value store itself should be as generic as possible, not
//! restricted to particular data structures.
//! We define legal crash states at this level and pass them
//! to the untrusted implementation, which passes them along
//! to untrusted components.
//!
//! Note that the design of this component is different from the original
//! verified log in that the untrusted implementation, rather than
//! the trusted implementation in this file, owns the
//! WriteRestrictedPersistentMemoryRegions backing the structures.
//! This makes the interface to the untrusted component simpler and
//! will make it easier to distinguish between regions owned by
//! different components.
//!
//! This file is unverified and should be tested/audited for correctness.
//!
//! TODO: handle errors properly in postconditions

#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use super::durable::durableimpl_v::*;
use super::durable::durablespec_t::*;
use super::kvimpl_v::*;
use super::kvspec_t::*;
use super::volatile::volatileimpl_v::*;
use super::volatile::volatilespec_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use std::hash::Hash;

verus! {

#[derive(Debug, PartialEq, Clone)]
pub enum KvError<K, E>
where
    K: std::fmt::Debug,
    E: std::fmt::Debug,
{
    NotImplemented,
    InvalidParameter,
    InternalError, // TODO: reason
    KeyNotFound,
    KeyAlreadyExists,
    InvalidKey{ key: K },
    IndexOutOfRange,
    RegionTooSmall { required: usize, actual: usize },
    OutOfSpace,
    InvalidPersistentMemoryRegionProvided, // TODO: reason
    SerializationError { error: E },
    DeserializationError { error: E },
}

pub trait Item<K> : Sized {
    spec fn spec_key(self) -> K;

    fn key(&self) -> (out: K)
        ensures
            out == self.spec_key()
    ;
}

// TODO: should the constructor take one PM region and break it up into the required sub-regions,
// or should the caller provide it split up in the way that they want?
pub struct KvStore<PM, K, I, L, D, V, E>
where
    PM: PersistentMemoryRegions,
    K: Hash + Eq + Clone + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Item<K> + Sized + std::fmt::Debug,
    L: PmCopy + std::fmt::Debug,
    D: DurableKvStore<PM, K, I, L, E>,
    V: VolatileKvIndex<K, E>,
    E: std::fmt::Debug,
{
    id: u128,
    untrusted_kv_impl: UntrustedKvStoreImpl<PM, K, I, L, D, V, E>,
}

// TODO: is there a better way to handle PhantomData?
#[verifier::external_body]
pub closed spec fn spec_phantom_data<V: ?Sized>() -> core::marker::PhantomData<V> {
    core::marker::PhantomData::default()
}

impl<PM, K, I, L, D, V, E> KvStore<PM, K, I, L, D, V, E>
where
    PM: PersistentMemoryRegions,
    K: Hash + Eq + Clone + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Item<K> + Sized + std::fmt::Debug,
    L: PmCopy + std::fmt::Debug,
    D: DurableKvStore<PM, K, I, L, E>,
    V: VolatileKvIndex<K, E>,
    E: std::fmt::Debug,
{
    pub closed spec fn view(&self) -> AbstractKvStoreState<K, I, L, E>
    {
        self.untrusted_kv_impl@
    }

    pub closed spec fn valid(self) -> bool
    {
        self.untrusted_kv_impl.valid()
    }

    /// The `KvStore` constructor calls the constructors for the durable and
    /// volatile components of the key-value store.
    /// `list_node_size` is the number of list entries in each node (not the number
    /// of bytes used by each node)
    fn new(
        pmem: PM,
        kvstore_id: u128,
        max_keys: usize,
        list_node_size: usize
    ) -> (result: Result<Self, KvError<K, E>>)
        requires
            pmem.inv(),
        ensures
            match result {
                Ok(new_kv) => {
                    &&& new_kv.valid()
                }
                Err(_) => true
            }
    {
        Ok(
            Self {
                id: kvstore_id,
                untrusted_kv_impl: UntrustedKvStoreImpl::untrusted_new(
                    pmem,
                    kvstore_id,
                    max_keys,
                    list_node_size
                )?
            }
        )
    }

    fn restore(pmem: PM, region_size: usize, kvstore_id: u128) -> (result: Result<Self, KvError<K, E>>)
        requires
            pmem.inv(),
        ensures
            match result {
                Ok(restored_kv) => {
                    let restored_state = UntrustedKvStoreImpl::<PM, K, I, L, D, V, E>::recover(pmem@.committed(), kvstore_id);
                    match restored_state {
                        Some(restored_state) => restored_kv@ == restored_state,
                        None => false
                    }
                }
                Err(_) => true // TODO
            }
    {
        Err(KvError::NotImplemented)
    }

    fn create(&mut self, key: &K, item: I) -> (result: Result<(), KvError<K, E>>)
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
        if self.untrusted_kv_impl.untrusted_contains_key(key) {
            Err(KvError::KeyAlreadyExists)
        } else {
            let tracked perm =
            TrustedKvPermission::new_two_possibilities(self.id, self@, self@.create(*key, item).unwrap());
            self.untrusted_kv_impl.untrusted_create(key, item, Tracked(&perm))
        }
    }

    fn read_item(&self, key: &K) -> (result: Option<&I>)
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

        self.untrusted_kv_impl.untrusted_read_item(key)
    }

    // fn read_item_and_list(&self, key: &K) -> (result: Option<(&I, Vec<&L>)>)
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
    //     self.untrusted_kv_impl.untrusted_read_item_and_list(key)
    // }

    fn read_list_entry_at_index(&self, key: &K, idx: u64) -> (result: Result<&L, KvError<K, E>>)
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
        self.untrusted_kv_impl.untrusted_read_list_entry_at_index(key, idx)
    }

    // fn read_list(&self, key: &K) -> (result: Option<&Vec<L>>)
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
    //     self.untrusted_kv_impl.untrusted_read_list(key)
    // }

    fn update_item(&mut self, key: &K, new_item: I) -> (result: Result<(), KvError<K, E>>)
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
        if self.untrusted_kv_impl.untrusted_contains_key(key) {
            let tracked perm = TrustedKvPermission::new_two_possibilities(self.id, self@, self@.update_item(*key, new_item).unwrap());
            self.untrusted_kv_impl.untrusted_update_item(key, new_item, Tracked(&perm))
        } else {
            Err(KvError::KeyNotFound)
        }

    }

    fn delete(&mut self, key: &K) -> (result: Result<(), KvError<K, E>>)
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
        if self.untrusted_kv_impl.untrusted_contains_key(key) {
            let tracked perm = TrustedKvPermission::new_two_possibilities(self.id, self@, self@.delete(*key).unwrap());
            self.untrusted_kv_impl.untrusted_delete(key, Tracked(&perm))
        } else {
            Err(KvError::KeyNotFound)
        }
    }

    // TODO: remove?
    fn append_to_list(
        &mut self,
        key: &K,
        new_list_entry: L
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
        if self.untrusted_kv_impl.untrusted_contains_key(key) {
            let tracked perm = TrustedKvPermission::new_two_possibilities(self.id, self@, self@.append_to_list(*key, new_list_entry).unwrap());
            self.untrusted_kv_impl.untrusted_append_to_list(key, new_list_entry, Tracked(&perm))
        } else {
            Err(KvError::KeyNotFound)
        }
    }

    fn append_to_list_and_update_item(
        &mut self,
        key: &K,
        new_list_entry: L,
        new_item: I,
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
        if self.untrusted_kv_impl.untrusted_contains_key(key) {
            let tracked perm = TrustedKvPermission::new_two_possibilities(self.id, self@, self@.append_to_list_and_update_item(*key, new_list_entry, new_item).unwrap());
            self.untrusted_kv_impl.untrusted_append_to_list_and_update_item(key,  new_list_entry, new_item, Tracked(&perm))
        } else {
            Err(KvError::KeyNotFound)
        }
    }

    fn update_list_entry_at_index(&mut self, key: &K, idx: usize, new_list_entry: L) -> (result: Result<(), KvError<K, E>>)
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
        if self.untrusted_kv_impl.untrusted_contains_key(key) {
            let tracked perm = TrustedKvPermission::new_two_possibilities(self.id, self@, self@.update_list_entry_at_index(*key, idx, new_list_entry).unwrap());
            self.untrusted_kv_impl.untrusted_update_list_entry_at_index(key, idx, new_list_entry, Tracked(&perm))
        } else {
            Err(KvError::KeyNotFound)
        }
    }

    fn update_entry_at_index_and_item(
        &mut self,
        key: &K,
        idx: usize,
        new_list_entry: L,
        new_item: I,
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
        if self.untrusted_kv_impl.untrusted_contains_key(key) {
            let tracked perm = TrustedKvPermission::new_two_possibilities(self.id, self@, self@.update_entry_at_index_and_item(*key, idx, new_list_entry, new_item).unwrap());
            self.untrusted_kv_impl.untrusted_update_entry_at_index_and_item(key,  idx, new_list_entry, new_item, Tracked(&perm))
        } else {
            Err(KvError::KeyNotFound)
        }
    }

    fn trim_list(
        &mut self,
        key: &K,
        trim_length: usize,
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
        if self.untrusted_kv_impl.untrusted_contains_key(key) {
            let tracked perm = TrustedKvPermission::new_two_possibilities(self.id, self@, self@.trim_list(*key, trim_length as int).unwrap());
            self.untrusted_kv_impl.untrusted_trim_list(key, trim_length, Tracked(&perm))
        } else {
            Err(KvError::KeyNotFound)
        }
    }

    fn trim_list_and_update_item(
        &mut self,
        key: &K,
        trim_length: usize,
        new_item: I,
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
        if self.untrusted_kv_impl.untrusted_contains_key(key) {
            let tracked perm = TrustedKvPermission::new_two_possibilities(self.id, self@, self@.trim_list_and_update_item(*key, trim_length as int, new_item).unwrap());
            self.untrusted_kv_impl.untrusted_trim_list_and_update_item(key, trim_length, new_item, Tracked(&perm))
        } else {
            Err(KvError::KeyNotFound)
        }
    }

    fn get_keys(&self) -> (result: Vec<K>)
        requires
            self.valid()
        ensures
            result@.to_set() == self@.get_keys()
    {
        self.untrusted_kv_impl.untrusted_get_keys()
    }
}

}
