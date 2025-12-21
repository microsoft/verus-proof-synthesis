//! This file contains functions for setting up persistent memory
//! regions for use in a multilog.
//!
//! The code in this file is verified and untrusted (as indicated by
//! the `_v.rs` suffix), so you don't have to read it to be confident
//! of the system's correctness.

use crate::log::inv_v::*;
use crate::log::layout_v::*;
use crate::log::logimpl_t::LogErr;
use crate::log::logspec_t::AbstractLogState;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::traits_t::size_of;
use builtin::*;
use builtin_macros::*;
use vstd::bytes::*;
use vstd::prelude::*;

verus! {

    // This function evaluates whether memory was correctly set up on
    // a region. It's a helpful specification function for use in
    // later functions in this file.
    //
    // Because answering this question depends on knowing various
    // metadata about this region and the log it's part of, the
    // function needs various input parameters for that. Its
    // parameters are:
    //
    // `mem` -- the contents of memory for this region
    // `region_size` -- how big this region is
    // `log_id` -- the GUID of the log it's being used for
    spec fn memory_correctly_set_up_on_region(
        mem: Seq<u8>,
        region_size: u64,
        log_id: u128,
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
        &&& global_metadata.program_guid == LOG_PROGRAM_GUID
        &&& global_metadata.version_number == LOG_PROGRAM_VERSION_NUMBER
        &&& global_metadata.length_of_region_metadata == RegionMetadata::spec_size_of()
        &&& region_metadata.region_size == region_size
        &&& region_metadata.log_id == log_id
        &&& region_metadata.log_area_len == region_size - ABSOLUTE_POS_OF_LOG_AREA
        &&& log_cdb == Some(false)
        &&& log_metadata.head == 0
        &&& log_metadata.log_length == 0
    }

    // This executable function sets up a single region for use in a
    // log. To do so, it needs various metadata about this region
    // and the log it's for, so it needs some parameters:
    //
    // `region_size`: how big this region is
    // `log_id`: the GUID of the log it's being used for
    //
    // It also needs the parameter `pm_region` that gives the
    // persistent memory region for us to write to.
    //
    // The main postcondition is:
    //
    // `memory_correctly_set_up_on_single_region(pm_regions@[which_log as int].flush().committed(),
    //                                           region_size, log_id, num_logs, which_log)`
    //
    // This means that, after the next flush, the memory in this
    // region will have been set up correctly. (This function doesn't
    // do the flush, for efficiency. That way we only need one flush
    // operation to flush all regions.)
    #[verifier::spinoff_prover]
    fn write_setup_metadata_to_region<PMRegion: PersistentMemoryRegion>(
        pm_region: &mut PMRegion,
        region_size: u64,
        log_id: u128,
    )
        requires
            old(pm_region).inv(),
            old(pm_region)@.no_outstanding_writes(),
            old(pm_region)@.len() == region_size,
            region_size >= ABSOLUTE_POS_OF_LOG_AREA + MIN_LOG_AREA_SIZE,
        ensures
            pm_region.inv(),
            pm_region.constants() == old(pm_region).constants(),
            memory_correctly_set_up_on_region(
                pm_region@.flush().committed(), // it'll be correct after the next flush
                region_size, log_id),
            metadata_types_set(pm_region@.flush().committed()),
    {
        broadcast use pmcopy_axioms;

        // Initialize global metadata and compute its CRC
        let global_metadata = GlobalMetadata {
            program_guid: LOG_PROGRAM_GUID,
            version_number: LOG_PROGRAM_VERSION_NUMBER,
            length_of_region_metadata: size_of::<RegionMetadata>() as u64,
        };
        let global_crc = calculate_crc(&global_metadata);

        // Initialize region metadata and compute its CRC
        let region_metadata = RegionMetadata {
            region_size,
            log_id,
            log_area_len: region_size - ABSOLUTE_POS_OF_LOG_AREA,
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

        assert(pm_region@.no_outstanding_writes());
        reveal(spec_padding_needed);
        // Write all metadata structures and their CRCs to memory
        pm_region.serialize_and_write(ABSOLUTE_POS_OF_GLOBAL_METADATA, &global_metadata);
        pm_region.serialize_and_write(ABSOLUTE_POS_OF_GLOBAL_CRC, &global_crc);
        pm_region.serialize_and_write(ABSOLUTE_POS_OF_REGION_METADATA, &region_metadata);
        pm_region.serialize_and_write(ABSOLUTE_POS_OF_REGION_CRC, &region_crc);
        pm_region.serialize_and_write(ABSOLUTE_POS_OF_LOG_CDB, &cdb);
        pm_region.serialize_and_write(ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE, &log_metadata);
        pm_region.serialize_and_write(ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE + size_of::<LogMetadata>() as u64, &log_crc);

        proof {
            // We want to prove that if we parse the result of
            // flushing memory, we get the desired metadata.

            // Prove that if we extract pieces of the flushed memory,
            // we get the little-endian encodings of the desired
            // metadata. By using the `=~=` operator, we get Z3 to
            // prove this by reasoning about per-byte equivalence.
            let mem = pm_region@.flush().committed();
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
            assert(extract_bytes(mem, ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as nat, LogMetadata::spec_size_of())
                   =~= log_metadata.spec_to_bytes());
            assert (extract_bytes(mem, ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_FALSE as nat, u64::spec_size_of())
                    =~= log_crc.spec_to_bytes());

            // Asserting these two postconditions here helps Verus finish out the proof.
            assert(memory_correctly_set_up_on_region(mem, region_size, log_id));
            assert(metadata_types_set(mem));
        }
    }

    // This exported executable function writes to persistent memory
    // all the metadata necessary to set up a log. To do so, it
    // needs some parameters:
    //
    // `region_size`: how big the region is
    //
    // `log_capacity`: what its capacity will be.
    // Note that this parameter is ghost because it's only needed to
    // establish the postcondition described below.
    //
    // `log_id`: the GUID of the log it's being used for
    //
    // It also needs the parameter `pm_region` that gives the
    // persistent memory region for us to write to.
    //
    // The main postcondition is:
    //
    // ```
    // recover_state(pm_region@.committed(), log_id) ==
    //     Some(AbstractLogState::initialize(log_capacity))
    // ```
    //
    // This means that if the recovery routine runs afterward, then
    // the resulting recovered abstract state will be the valid
    // initial value
    // `AbstractLogState::initialize(log_capacity)`.
    #[verifier::spinoff_prover]
    pub fn write_setup_metadata<PMRegion: PersistentMemoryRegion>(
        pm_region: &mut PMRegion,
        region_size: u64,
        Ghost(log_capacity): Ghost<u64>,
        log_id: u128,
    )
        requires
            old(pm_region).inv(),
            old(pm_region)@.len() == region_size,
            old(pm_region)@.len() >= ABSOLUTE_POS_OF_LOG_AREA + MIN_LOG_AREA_SIZE,
            old(pm_region)@.len() == log_capacity + ABSOLUTE_POS_OF_LOG_AREA,
            old(pm_region)@.no_outstanding_writes(),
        ensures
            pm_region.inv(),
            pm_region.constants() == old(pm_region).constants(),
            pm_region@.len() == old(pm_region)@.len(),
            pm_region@.no_outstanding_writes(),
            recover_state(pm_region@.committed(), log_id) == Some(AbstractLogState::initialize(log_capacity as int)),
            metadata_types_set(pm_region@.committed()),
    {
        write_setup_metadata_to_region(pm_region, region_size, log_id);

        proof {
            // First, establish that recovering after a flush will get
            // abstract state
            // `AbstractLogState::initialize(log_capacity)`.

            let flushed_region = pm_region@.flush();
            let pm_region_committed = flushed_region.committed();
            assert(recover_state(pm_region_committed, log_id)
                   =~= Some(AbstractLogState::initialize(log_capacity as int))) by {
                assert(pm_region_committed.len() == pm_region@.len());
                assert(pm_region_committed == pm_region@.flush().committed());
                assert(recover_log(pm_region_committed, log_capacity as int, 0int, 0int) =~=
                       Some(AbstractLogState::initialize(log_capacity as int)));
            }

            // Second, establish that the flush we're about to do
            // won't change regions' lengths.
            assert(pm_region@.len() == flushed_region.len());
        }

        pm_region.flush()
    }

}
