//! This file contains the trusted implementation for
//! `VolatileMemoryMockingPersistentMemoryRegions`, a collection of
//! volatile memory regions. It serves as a mock of persistent memory
//! regions by implementing trait `PersistentMemoryRegions`.
//!
//! THIS IS ONLY INTENDED FOR USE IN TESTING! In practice, one should
//! use actually persistent memory to implement persistent memory!

use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use builtin::*;
use builtin_macros::*;
use deps_hack::rand::Rng;
use std::convert::*;
use vstd::prelude::*;

verus! {

    // The `VolatileMemoryMockingPersistentMemoryRegion` struct
    // contains a vector of volatile memory to hold the contents, as
    // well as a ghost field that keeps track of the virtual modeled
    // state. This ghost field pretends that outstanding writes remain
    // outstanding even though in the concrete `contents` field we
    // actually overwrite all data in place immediately.
    pub struct VolatileMemoryMockingPersistentMemoryRegion
    {
        contents: Vec<u8>,
    }

    impl VolatileMemoryMockingPersistentMemoryRegion
    {
        #[verifier::external_body]
        fn new(region_size: u64) -> (result: Self)
            ensures
                result.inv(),
                result@.len() == region_size,
        {
            let contents: Vec<u8> = vec![0; region_size as usize];
            Self { contents }
        }
    }

    impl PersistentMemoryRegion for VolatileMemoryMockingPersistentMemoryRegion
    {
        #[verifier::external_body]
        closed spec fn view(&self) -> PersistentMemoryRegionView;

        closed spec fn inv(&self) -> bool
        {
            // We maintain the invariant that our size fits in a `u64`.
            &&& self.contents.len() <= u64::MAX
            &&& self.contents.len() == self@.len()

            // We also maintain the invariant that the contents of our
            // volatile buffer matches the result of flushing the
            // abstract state.
            &&& self.contents@ == self@.flush().committed()
        }

        closed spec fn constants(&self) -> PersistentMemoryConstants;

        fn get_region_size(&self) -> (result: u64)
        {
            self.contents.len() as u64
        }

        #[verifier::external_body]
        fn read_aligned<S>(&self, addr: u64) -> (bytes: Result<MaybeCorruptedBytes<S>, PmemError>)
            where 
                S: PmCopy 
        {
            let pm_slice = &self.contents[addr as usize..addr as usize + S::size_of() as usize];
            let ghost addrs = Seq::new(S::spec_size_of() as nat, |i: int| addr + i);
            let ghost true_bytes = self@.committed().subrange(addr as int, addr + S::size_of());
            let ghost true_val = S::spec_from_bytes(true_bytes);

            let mut maybe_corrupted_val = MaybeCorruptedBytes::new();
            maybe_corrupted_val.copy_from_slice(pm_slice, Ghost(true_val), Ghost(addrs),
                                                Ghost(self.constants().impervious_to_corruption));

            Ok(maybe_corrupted_val)
        }

        #[verifier::external_body]
        fn read_unaligned(&self, addr: u64, num_bytes: u64) -> (bytes: Result<Vec<u8>, PmemError>)
        {
            let pm_slice = &self.contents[addr as usize..addr as usize + num_bytes as usize];
            let unaligned_buffer = copy_from_slice(pm_slice);
            Ok(unaligned_buffer)
        }

        #[verifier::external_body]
        fn write(&mut self, addr: u64, bytes: &[u8])
        {
            let addr_usize: usize = addr.try_into().unwrap();
            self.contents.splice(addr_usize..addr_usize+bytes.len(), bytes.iter().cloned());
        }

        #[verifier::external_body]
        fn serialize_and_write<S>(&mut self, addr: u64, to_write: &S)
            where
                S: PmCopy + Sized
        {
            let addr_usize: usize = addr.try_into().unwrap();
            let num_bytes: usize = S::size_of().try_into().unwrap();
            let s_pointer = to_write as *const S;
            let bytes_pointer = s_pointer as *const u8;
            // SAFETY: `bytes_pointer` always points to `num_bytes` consecutive, initialized
            // bytes because it was obtained by casting a regular Rust object reference
            // to a raw pointer. The borrow checker will ensure that `to_write` is not modified
            // by someone else during this function.
            let bytes = unsafe {
                std::slice::from_raw_parts(bytes_pointer, num_bytes)
            };
            self.contents.splice(addr_usize..addr_usize+num_bytes, bytes.iter().cloned());
        }

        #[verifier::external_body]
        fn flush(&mut self)
        {
        }
    }

    // The `VolatileMemoryMockingPersistentMemoryRegions` struct
    // contains a vector of volatile memory regions.
    pub struct VolatileMemoryMockingPersistentMemoryRegions
    {
        pub regions: Vec<VolatileMemoryMockingPersistentMemoryRegion>,
    }

    impl VolatileMemoryMockingPersistentMemoryRegions
    {
        #[verifier::external_body]
        pub fn new(region_sizes: &[u64]) -> (result: Self)
            ensures
                result.inv(),
                result@.len() == region_sizes@.len(),
                forall |i| 0 <= i < region_sizes@.len() ==> #[trigger] result@[i].len() == region_sizes[i],
        {
            let mut regions = Vec::<VolatileMemoryMockingPersistentMemoryRegion>::new();
            let num_regions = region_sizes.len();
            for pos in 0..num_regions
                invariant
                    regions.len() == pos,
                    forall |i| 0 <= i < pos ==> regions[i]@.len() == region_sizes[i],
            {
                let region = VolatileMemoryMockingPersistentMemoryRegion::new(region_sizes[pos]);
                regions.push(region);
            }
            Self{ regions }
        }
    }

    /// So that `VolatileMemoryMockingPersistentMemoryRegions` can be
    /// used to mock a collection of persistent memory regions, it
    /// implements the trait `PersistentMemoryRegions`.
    impl PersistentMemoryRegions for VolatileMemoryMockingPersistentMemoryRegions {
        #[verifier::external_body]
        closed spec fn view(&self) -> PersistentMemoryRegionsView
        {
            PersistentMemoryRegionsView{
                regions: self.regions@.map(|_i, r: VolatileMemoryMockingPersistentMemoryRegion| r@)
            }
        }

        closed spec fn inv(&self) -> bool
        {
            forall |i| 0 <= i < self.regions.len() ==> #[trigger] self.regions[i].inv()
        }

        #[verifier::external_body]
        closed spec fn constants(&self) -> PersistentMemoryConstants;

        #[verifier::external_body]
        fn get_num_regions(&self) -> usize
        {
            self.regions.len()
        }

        #[verifier::external_body]
        fn get_region_size(&self, index: usize) -> u64
        {
            self.regions[index].get_region_size()
        }

        #[verifier::external_body]
        fn read_aligned<S>(&self, index: usize, addr: u64) -> (bytes: Result<MaybeCorruptedBytes<S>, PmemError>)
            where 
                S: PmCopy
        {
            self.regions[index].read_aligned::<S>(addr)
        }

        #[verifier::external_body]
        fn read_unaligned(&self, index: usize, addr: u64, num_bytes: u64) -> (bytes: Result<Vec<u8>, PmemError>)
        {
            self.regions[index].read_unaligned(addr, num_bytes)
        }

        #[verifier::external_body]
        fn write(&mut self, index: usize, addr: u64, bytes: &[u8])
        {
            self.regions[index].write(addr, bytes)
        }

        #[verifier::external_body]
        fn serialize_and_write<S>(&mut self, index: usize, addr: u64, to_write: &S)
            where
                S: PmCopy + Sized
        {
            self.regions[index].serialize_and_write(addr, to_write);
        }

        #[verifier::external_body]
        fn flush(&mut self)
        {
        }
    }
}
