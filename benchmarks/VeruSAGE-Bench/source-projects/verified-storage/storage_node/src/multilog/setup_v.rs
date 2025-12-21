//! This file contains functions for setting up persistent memory
//! regions for use in a multilog.
//!
//! The code in this file is verified and untrusted (as indicated by
//! the `_v.rs` suffix), so you don't have to read it to be confident
//! of the system's correctness.

use crate::log::inv_v::lemma_auto_smaller_range_of_seq_is_subrange;
use crate::multilog::layout_v::*;
use crate::multilog::multilogimpl_t::MultiLogErr;
use crate::multilog::multilogspec_t::{AbstractLogState, AbstractMultiLogState};
use crate::multilog::inv_v::*;
use crate::pmem::crc_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::traits_t::size_of;
use builtin::*;
use builtin_macros::*;
use vstd::bytes::*;
use vstd::prelude::*;

verus! {

    // This exported executable function checks whether there's enough
    // space on persistent memory regions to support a multilog.
    //
    // `region_sizes` -- a vector of sizes, one per region
    // `num_regions` -- the number of regions (equal to the length of the `region_sizes` array)
    //
    // The return value is a `Result<(), MultiLogErr>`, meaning the following:
    //
    // `Ok(())` -- there's enough space on each region
    // `Err(err)` -- there isn't enough space, so the caller should return the error `err`.
    pub fn check_for_required_space(region_sizes: &Vec<u64>, num_regions: u32) -> (result: Result<(), MultiLogErr>)
        requires
            num_regions == region_sizes.len()
        ensures
            ({
                match result {
                    Ok(()) => forall |i| 0 <= i < region_sizes@.len() ==>
                        region_sizes[i] >= ABSOLUTE_POS_OF_LOG_AREA + MIN_LOG_AREA_SIZE,
                    Err(MultiLogErr::InsufficientSpaceForSetup{ which_log, required_space }) => {
                        &&& 0 <= which_log < region_sizes@.len()
                        &&& region_sizes[which_log as int] < required_space
                        &&& required_space == ABSOLUTE_POS_OF_LOG_AREA + MIN_LOG_AREA_SIZE
                    },
                    _ => false,
                }
            })
    {
        // Loop through all the regions, checking for sufficiency of
        // size.

        for which_log in 0..num_regions
            invariant
                num_regions == region_sizes.len(),
                forall |j| 0 <= j < which_log ==> region_sizes[j] >= ABSOLUTE_POS_OF_LOG_AREA + MIN_LOG_AREA_SIZE
        {
            if region_sizes[which_log as usize] < ABSOLUTE_POS_OF_LOG_AREA + MIN_LOG_AREA_SIZE {
                return Err(MultiLogErr::InsufficientSpaceForSetup{
                    which_log,
                    required_space: ABSOLUTE_POS_OF_LOG_AREA + MIN_LOG_AREA_SIZE
                });
            }
        }
        Ok(())
    }

    // This exported function computes the log capacities allowed by the given region sizes.
    pub fn compute_log_capacities(region_sizes: &Vec<u64>) -> (result: Vec<u64>)
        requires
            forall |i: int| 0 <= i < region_sizes.len() ==> region_sizes[i] >= ABSOLUTE_POS_OF_LOG_AREA + MIN_LOG_AREA_SIZE
        ensures
            result.len() == region_sizes.len(),
            forall |i: int| 0 <= i < region_sizes.len() ==>
                #[trigger] result[i] + ABSOLUTE_POS_OF_LOG_AREA == region_sizes[i]
    {
        let mut result = Vec::<u64>::new();
        for which_region in iter: 0..region_sizes.len()
            invariant
                iter.end == region_sizes.len(),
                forall |i: int| 0 <= i < region_sizes.len() ==> region_sizes[i] >= ABSOLUTE_POS_OF_LOG_AREA + MIN_LOG_AREA_SIZE,
                result.len() == which_region,
                forall |i: int| 0 <= i < which_region ==>
                    #[trigger] result[i] + ABSOLUTE_POS_OF_LOG_AREA == region_sizes[i]
        {
            result.push(region_sizes[which_region] - ABSOLUTE_POS_OF_LOG_AREA);
        }
        result
    }

    // This function evaluates whether memory was correctly set up on
    // a single region. It's a helpful specification function for use
    // in later functions in this file.
    //
    // Because answering this question depends on knowing various
    // metadata about this region and the multilog it's part of, the
    // function needs various input parameters for that. Its
    // parameters are:
    //
    // `mem` -- the contents of memory for this region
    // `region_size` -- how big this region is
    // `multilog_id` -- the GUID of the multilog it's being used for
    // `num_logs` -- the number of logs in the multilog
    // `which_log` -- which among those logs this region is for
    spec fn memory_correctly_set_up_on_single_region(
        mem: Seq<u8>,
        region_size: u64,
        multilog_id: u128,
        num_logs: u32,
        which_log: u32,
    ) -> bool
    {
        let global_crc = deserialize_global_crc(mem);
        let global_metadata = deserialize_global_metadata(mem);
        let region_crc = deserialize_region_crc(mem);
        let region_metadata = deserialize_region_metadata(mem);
        let log_cdb = deserialize_and_check_log_cdb(mem);
        let log_metadata = deserialize_log_metadata(mem, false);
        let log_crc = deserialize_log_crc(mem, false);
        &&& mem.len() >= ABSOLUTE_POS_OF_LOG_AREA + MIN_LOG_AREA_SIZE
        &&& mem.len() == region_size
        &&& global_crc == global_metadata.spec_crc()
        &&& region_crc == region_metadata.spec_crc()
        &&& log_crc == log_metadata.spec_crc()
        &&& global_metadata.program_guid == MULTILOG_PROGRAM_GUID
        &&& global_metadata.version_number == MULTILOG_PROGRAM_VERSION_NUMBER
        &&& global_metadata.length_of_region_metadata == RegionMetadata::spec_size_of()
        &&& region_metadata.region_size == region_size
        &&& region_metadata.multilog_id == multilog_id
        &&& region_metadata.num_logs == num_logs
        &&& region_metadata.which_log == which_log
        &&& region_metadata.log_area_len == region_size - ABSOLUTE_POS_OF_LOG_AREA
        &&& log_cdb == Some(false)
        &&& log_metadata.head == 0
        &&& log_metadata.log_length == 0
    }

    // This executable function sets up a single region for use in a
    // multilog. To do so, it needs various metadata about this region
    // and the multilog it's part of, so it needs some parameters:
    //
    // `region_size`: how big this region is
    // `multilog_id`: the GUID of the multilog it's being used for
    // `num_logs`: the number of logs in the multilog
    // `which_log`: which among those logs this region is for
    //
    // It also needs the parameter `pm_regions` that gives the
    // persistent memory regions for us to write to. It'll only write
    // to region number `which_log`.
    //
    // The main postcondition is:
    //
    // `memory_correctly_set_up_on_single_region(pm_regions@[which_log as int].flush().committed(),
    //                                           region_size, multilog_id, num_logs, which_log)`
    //
    // This means that, after the next flush, the memory in this
    // region will have been set up correctly. (This function doesn't
    // do the flush, for efficiency. That way we only need one flush
    // operation to flush all regions.)
    fn write_setup_metadata_to_single_region<PMRegions: PersistentMemoryRegions>(
        pm_regions: &mut PMRegions,
        region_size: u64,
        multilog_id: u128,
        num_logs: u32,
        which_log: u32,
    )
        requires
            old(pm_regions).inv(),
            num_logs == old(pm_regions)@.len(),
            which_log < num_logs,
            old(pm_regions)@[which_log as int].no_outstanding_writes(),
            old(pm_regions)@[which_log as int].len() == region_size,
            region_size >= ABSOLUTE_POS_OF_LOG_AREA + MIN_LOG_AREA_SIZE,
            which_log != 0,
        ensures
            pm_regions.inv(),
            pm_regions.constants() == old(pm_regions).constants(),
            pm_regions@.len() == old(pm_regions)@.len(),
            forall |i: int| 0 <= i < pm_regions@.len() && i != which_log ==> pm_regions@[i] =~= old(pm_regions)@[i],
            memory_correctly_set_up_on_single_region(
                pm_regions@[which_log as int].flush().committed(), // it'll be correct after the next flush
                region_size, multilog_id, num_logs, which_log),
            metadata_types_set_in_region(pm_regions@[which_log as int].flush().committed(), false),
    {
        broadcast use pmcopy_axioms;
        reveal(spec_padding_needed);

        // Initialize global metadata and compute its CRC
        // We write this out for each log so that if, upon restore, our caller accidentally
        // sends us the wrong regions, we can detect it.
        let global_metadata = GlobalMetadata {
            program_guid: MULTILOG_PROGRAM_GUID,
            version_number: MULTILOG_PROGRAM_VERSION_NUMBER,
            length_of_region_metadata: size_of::<RegionMetadata>() as u64,
        };
        let global_crc = calculate_crc(&global_metadata);

        // Initialize region metadata and compute its CRC
        let region_metadata = RegionMetadata {
            region_size,
            multilog_id,
            num_logs,
            which_log,
            log_area_len: region_size - ABSOLUTE_POS_OF_LOG_AREA,
            _padding: 0,
        };
        let region_crc = calculate_crc(&region_metadata);

        // Obtain the initial CDB value
        let cdb = CDB_FALSE;

        // Initialize log metadata and compute its CRC
        let log_metadata = LogMetadata {
            head: 0,
            _padding: 0,
            log_length: 0
        };
        let log_crc = calculate_crc(&log_metadata);

        // Write all metadata structures and their CRCs to memory
        pm_regions.serialize_and_write(which_log as usize, ABSOLUTE_POS_OF_GLOBAL_METADATA, &global_metadata);
        pm_regions.serialize_and_write(which_log as usize, ABSOLUTE_POS_OF_GLOBAL_CRC, &global_crc);
        pm_regions.serialize_and_write(which_log as usize, ABSOLUTE_POS_OF_REGION_METADATA, &region_metadata);
        pm_regions.serialize_and_write(which_log as usize, ABSOLUTE_POS_OF_REGION_CRC, &region_crc);
        pm_regions.serialize_and_write(which_log as usize, ABSOLUTE_POS_OF_LOG_CDB, &cdb);
        pm_regions.serialize_and_write(which_log as usize, ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE, &log_metadata);
        pm_regions.serialize_and_write(which_log as usize, ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_FALSE, &log_crc);

        proof {
            // We want to prove that if we parse the result of
            // flushing memory, we get the desired metadata. 

            // Prove that if we extract pieces of the flushed memory,
            // we get the little-endian encodings of the desired
            // metadata. By using the `=~=` operator, we get Z3 to
            // prove this by reasoning about per-byte equivalence.

            let mem = pm_regions@[which_log as int].flush().committed();
            assert(extract_bytes(mem, ABSOLUTE_POS_OF_GLOBAL_METADATA as nat, GlobalMetadata::spec_size_of())
                   =~= global_metadata.spec_to_bytes());
            assert(extract_bytes(mem, ABSOLUTE_POS_OF_GLOBAL_CRC as nat, u64::spec_size_of())
                   =~= global_crc.spec_to_bytes());
            assert(extract_bytes(mem, ABSOLUTE_POS_OF_REGION_METADATA as nat, RegionMetadata::spec_size_of())
                   =~= region_metadata.spec_to_bytes());
            assert(extract_bytes(mem, ABSOLUTE_POS_OF_REGION_CRC as nat, u64::spec_size_of())
                   =~= region_crc.spec_to_bytes());
            assert(extract_bytes(mem, ABSOLUTE_POS_OF_LOG_CDB as nat, u64::spec_size_of())
                   =~= CDB_FALSE.spec_to_bytes());
            assert(extract_bytes(mem, ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as nat,
                                 LogMetadata::spec_size_of())
                   =~= log_metadata.spec_to_bytes());
            assert (extract_bytes(mem, ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_FALSE as nat, u64::spec_size_of())
                    =~= log_crc.spec_to_bytes());
        }
    }

    fn write_setup_metadata_to_first_region<PMRegions: PersistentMemoryRegions>(
        pm_regions: &mut PMRegions,
        region_size: u64,
        multilog_id: u128,
        num_logs: u32,
    )
        requires
            old(pm_regions).inv(),
            num_logs == old(pm_regions)@.len(),
            0 < num_logs,
            old(pm_regions)@[0].no_outstanding_writes(),
            old(pm_regions)@[0].len() == region_size,
            region_size >= ABSOLUTE_POS_OF_LOG_AREA + MIN_LOG_AREA_SIZE,
            
        ensures
            pm_regions.inv(),
            pm_regions.constants() == old(pm_regions).constants(),
            pm_regions@.len() == old(pm_regions)@.len(),
            forall |i: int| 1 <= i < pm_regions@.len() ==> pm_regions@[i] =~= old(pm_regions)@[i],
            memory_correctly_set_up_on_single_region(
                pm_regions@[0].flush().committed(), // it'll be correct after the next flush
                region_size, multilog_id, num_logs, 0),
            metadata_types_set_in_first_region(pm_regions@[0].flush().committed()),
            metadata_types_set_in_region(pm_regions@[0].flush().committed(), false),
            deserialize_and_check_log_cdb(pm_regions@[0].flush().committed()) is Some,
            !deserialize_and_check_log_cdb(pm_regions@[0].flush().committed()).unwrap(),
    {
        broadcast use pmcopy_axioms;
        reveal(spec_padding_needed);

        // Initialize global metadata and compute its CRC
        // We write this out for each log so that if, upon restore, our caller accidentally
        // sends us the wrong regions, we can detect it.
        let global_metadata = GlobalMetadata {
            program_guid: MULTILOG_PROGRAM_GUID,
            version_number: MULTILOG_PROGRAM_VERSION_NUMBER,
            length_of_region_metadata: size_of::<RegionMetadata>() as u64,
        };
        let global_crc = calculate_crc(&global_metadata);

        // Initialize region metadata and compute its CRC
        let region_metadata = RegionMetadata {
            region_size,
            multilog_id,
            num_logs,
            which_log: 0,
            log_area_len: region_size - ABSOLUTE_POS_OF_LOG_AREA,
            _padding: 0,
        };
        let region_crc = calculate_crc(&region_metadata);

        // Obtain the initial CDB value
        let cdb = CDB_FALSE;

        // Initialize log metadata and compute its CRC
        let log_metadata = LogMetadata {
            head: 0,
            _padding: 0,
            log_length: 0
        };
        let log_crc = calculate_crc(&log_metadata);

        // Write all metadata structures and their CRCs to memory
        pm_regions.serialize_and_write(0, ABSOLUTE_POS_OF_GLOBAL_METADATA, &global_metadata);
        pm_regions.serialize_and_write(0, ABSOLUTE_POS_OF_GLOBAL_CRC, &global_crc);
        pm_regions.serialize_and_write(0, ABSOLUTE_POS_OF_REGION_METADATA, &region_metadata);
        pm_regions.serialize_and_write(0, ABSOLUTE_POS_OF_REGION_CRC, &region_crc);
        pm_regions.serialize_and_write(0, ABSOLUTE_POS_OF_LOG_CDB, &cdb);
        pm_regions.serialize_and_write(0, ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE, &log_metadata);
        pm_regions.serialize_and_write(0, ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_FALSE, &log_crc);

        proof {
            // We want to prove that if we parse the result of
            // flushing memory, we get the desired metadata. 

            // Prove that if we extract pieces of the flushed memory,
            // we get the little-endian encodings of the desired
            // metadata. By using the `=~=` operator, we get Z3 to
            // prove this by reasoning about per-byte equivalence.

            let mem = pm_regions@[0].flush().committed();
            assert(extract_bytes(mem, ABSOLUTE_POS_OF_GLOBAL_METADATA as nat, GlobalMetadata::spec_size_of())
                   =~= global_metadata.spec_to_bytes());
            assert(extract_bytes(mem, ABSOLUTE_POS_OF_GLOBAL_CRC as nat, u64::spec_size_of())
                   =~= global_crc.spec_to_bytes());
            assert(extract_bytes(mem, ABSOLUTE_POS_OF_REGION_METADATA as nat, RegionMetadata::spec_size_of())
                   =~= region_metadata.spec_to_bytes());
            assert(extract_bytes(mem, ABSOLUTE_POS_OF_REGION_CRC as nat, u64::spec_size_of())
                   =~= region_crc.spec_to_bytes());
            assert(extract_bytes(mem, ABSOLUTE_POS_OF_LOG_CDB as nat, u64::spec_size_of())
                   =~= CDB_FALSE.spec_to_bytes());
            assert(extract_bytes(mem, ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as nat,
                                 LogMetadata::spec_size_of())
                   =~= log_metadata.spec_to_bytes());
            assert (extract_bytes(mem, ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_FALSE as nat, u64::spec_size_of())
                    =~= log_crc.spec_to_bytes());

            assert(metadata_types_set_in_first_region(pm_regions@[0].flush().committed()));
        }
    }

    // This exported executable function writes to persistent memory
    // all the metadata necessary to set up a multilog. To do so, it
    // needs some parameters:
    //
    // `region_sizes`: for each region, how big it is
    //
    // `log_capacities`: for each region, what its capacity will be.
    // Note that this parameter is ghost because it's only needed to
    // establish the postcondition described below.
    //
    // `multilog_id`: the GUID of the multilog it's being used for
    //
    // It also needs the parameter `pm_regions` that gives the
    // persistent memory regions for us to write to.
    //
    // The main postcondition is:
    //
    // ```
    // recover_all(pm_regions@.committed(), multilog_id) ==
    //     Some(AbstractMultiLogState::initialize(log_capacities))
    // ```
    //
    // This means that if the recovery routine runs afterward, then
    // the resulting recovered abstract state will be the valid
    // initial value
    // `AbstractMultiLogState::initialize(log_capacities)`.
    pub fn write_setup_metadata_to_all_regions<PMRegions: PersistentMemoryRegions>(
        pm_regions: &mut PMRegions,
        region_sizes: &Vec<u64>,
        Ghost(log_capacities): Ghost<Seq<u64>>,
        multilog_id: u128,
    )
        requires
            old(pm_regions).inv(),
            old(pm_regions)@.len() == region_sizes@.len() == log_capacities.len(),
            1 <= old(pm_regions)@.len() <= u32::MAX,
            forall |i: int| #[trigger] log_index_trigger(i) && 0 <= i < old(pm_regions)@.len() ==>
                old(pm_regions)@[i].len() == region_sizes@[i],
            forall |i: int| #[trigger] log_index_trigger(i) && 0 <= i < old(pm_regions)@.len() ==>
                old(pm_regions)@[i].len() >= ABSOLUTE_POS_OF_LOG_AREA + MIN_LOG_AREA_SIZE,
            forall |i: int| #[trigger] log_index_trigger(i) && 0 <= i < old(pm_regions)@.len() ==>
                old(pm_regions)@[i].len() == log_capacities[i] + ABSOLUTE_POS_OF_LOG_AREA,
            old(pm_regions)@.no_outstanding_writes(),
        ensures
            pm_regions.inv(),
            pm_regions.constants() == old(pm_regions).constants(),
            pm_regions@.len() == old(pm_regions)@.len(),
            forall |i: int| #[trigger] log_index_trigger(i) && 0 <= i < pm_regions@.len() ==>
                pm_regions@[i].len() == old(pm_regions)@[i].len(),
            pm_regions@.no_outstanding_writes(),
            recover_all(pm_regions@.committed(), multilog_id) == Some(AbstractMultiLogState::initialize(log_capacities)),
            metadata_types_set(pm_regions@.committed()),
    {
        // Loop `which_log` from 0 to `region_sizes.len() - 1`, each time
        // setting up the metadata for region `which_log`.

        let ghost old_pm_regions = pm_regions@;
        let num_logs = region_sizes.len() as u32;

        // the first region is set up differently, so we do it outside of the loop to make the loop invariant
        // easier to maintain
        assert(log_index_trigger(0));
        let region_size: u64 = region_sizes[0];
        assert (region_size == pm_regions@[0].len());
        write_setup_metadata_to_first_region(pm_regions, region_size, multilog_id, num_logs);

        for which_log in 1..num_logs
            invariant
                num_logs == pm_regions@.len(),
                pm_regions.inv(),
                pm_regions.constants() == old(pm_regions).constants(),
                pm_regions@.len() == old(pm_regions)@.len() == region_sizes@.len() == log_capacities.len(),
                pm_regions@.len() >= 1,
                pm_regions@.len() <= u32::MAX,
                forall |i: int| #[trigger] log_index_trigger(i) && 0 <= i < pm_regions@.len() ==>
                    pm_regions@[i].len() == old(pm_regions)@[i].len(),
                forall |i: int| #[trigger] log_index_trigger(i) && 0 <= i < pm_regions@.len() ==>
                    pm_regions@[i].len() == region_sizes@[i],
                forall |i: int| #[trigger] log_index_trigger(i) && 0 <= i < pm_regions@.len() ==>
                    pm_regions@[i].len() >= ABSOLUTE_POS_OF_LOG_AREA + MIN_LOG_AREA_SIZE,
                forall |i: int| #[trigger] log_index_trigger(i) && 0 <= i < pm_regions@.len() ==>
                    pm_regions@[i].len() == log_capacities[i] + ABSOLUTE_POS_OF_LOG_AREA,
                forall |i: int| #[trigger] log_index_trigger(i) && which_log <= i < pm_regions@.len() ==>
                    pm_regions@[i].no_outstanding_writes(),
                // The key invariant is that every region less than `which_log` has been set up correctly.
                forall |i: u32| #[trigger] log_index_trigger(i as int) && i < which_log ==>
                    memory_correctly_set_up_on_single_region(pm_regions@[i as int].flush().committed(),
                                                             region_sizes@[i as int], multilog_id, num_logs, i),
                metadata_types_set_in_first_region(pm_regions@[0].flush().committed()),
                forall |i: u32| #[trigger] log_index_trigger(i as int) && i < which_log ==>
                    metadata_types_set_in_region(pm_regions@[i as int].flush().committed(), false),
        {
            assert(log_index_trigger(which_log as int));
            let region_size: u64 = region_sizes[which_log as usize];
            assert (region_size == pm_regions@[which_log as int].len());
            write_setup_metadata_to_single_region(pm_regions, region_size, multilog_id, num_logs, which_log);
        }

        proof {
            // First, establish that recovering after a flush will get
            // abstract state
            // `AbstractMultiLogState::initialize(log_capacities)`.

            let flushed_regions = pm_regions@.flush();
            let pm_regions_committed = flushed_regions.committed();
            assert(recover_all(pm_regions_committed, multilog_id)
                   =~= Some(AbstractMultiLogState::initialize(log_capacities))) by {
                // We have to use the trigger `pm_regions_committed[i]` to reason about
                // what happens in the sequence interpolation in `recover_all`.
                assert(forall |i: int| log_index_trigger(i) && 0 <= i < pm_regions_committed.len() ==>
                       recover_abstract_log_from_region_given_cdb(#[trigger] pm_regions_committed[i], multilog_id,
                                                                  pm_regions_committed.len() as int, i, false) ==
                       Some(AbstractLogState::initialize(log_capacities[i] as int)));
            }

            // Second, establish that the flush we're about to do
            // won't change regions' lengths.
            assert(forall |i: int| #[trigger] log_index_trigger(i) && 0 <= i < pm_regions@.len() ==>
                   pm_regions@[i].len() == flushed_regions[i].len());
            
            // Finally, help Verus establish that the metadata types are set for all regions
            lemma_metadata_types_set_flush_committed(pm_regions@, false);
            assert(metadata_types_set(pm_regions@.flush().committed()));
        }

        pm_regions.flush()
    }

}
