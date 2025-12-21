//! This file contains functions describing invariants of a
//! `UntrustedLogImpl`, as well as lemmas about those invariants.
//!
//! The code in this file is verified and untrusted (as indicated by
//! the `_v.rs` suffix), so you don't have to read it to be confident
//! of the system's correctness.
//!
use crate::log::layout_v::*;
use crate::log::logimpl_v::LogInfo;
use crate::log::logspec_t::AbstractLogState;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::subregion_v::*;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

verus! {

    // This invariant says that there are no outstanding writes to any
    // part of the metadata subregion of the persistent-memory region.
    // It's temporarily violated in the middle of various operations,
    // of course, but it's always restored before finishing an
    // operation.
    pub open spec fn no_outstanding_writes_to_metadata(
        pm_region_view: PersistentMemoryRegionView,
    ) -> bool
    {
        pm_region_view.no_outstanding_writes_in_range(ABSOLUTE_POS_OF_GLOBAL_METADATA as int,
                                                      ABSOLUTE_POS_OF_LOG_AREA as int)
    }

    // This invariant is similar to no_outstanding_writes_to_metadata, except that it allows outstanding writes
    // to the inactive log metadata region.
    pub open spec fn no_outstanding_writes_to_active_metadata(
        pm_region_view: PersistentMemoryRegionView,
        cdb: bool,
    ) -> bool 
    {
        // Note that we include the active log metadata's CRC in the region
        let metadata_pos = if cdb { ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_TRUE as int }
                           else { ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as int };
        &&& pm_region_view.no_outstanding_writes_in_range(
            metadata_pos,
            metadata_pos + LogMetadata::spec_size_of() + u64::spec_size_of()
        )
        &&& pm_region_view.no_outstanding_writes_in_range(ABSOLUTE_POS_OF_GLOBAL_METADATA as int,
                                                        ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as int)
    }

    pub open spec fn active_metadata_is_equal(
        pm_region_view1: PersistentMemoryRegionView,
        pm_region_view2: PersistentMemoryRegionView,
    ) -> bool 
    {
        let pm_bytes1 = pm_region_view1.committed();
        let pm_bytes2 = pm_region_view2.committed();
        active_metadata_bytes_are_equal(pm_bytes1, pm_bytes2)
    }

    pub open spec fn active_metadata_bytes_are_equal(
        pm_bytes1: Seq<u8>,
        pm_bytes2: Seq<u8>,
    ) -> bool {
        let cdb1 = deserialize_and_check_log_cdb(pm_bytes1);
        let cdb2 = deserialize_and_check_log_cdb(pm_bytes2);

        &&& cdb1.is_Some()
        &&& cdb2.is_Some()
        &&& cdb1 == cdb2 
        &&& pm_bytes1.subrange(ABSOLUTE_POS_OF_GLOBAL_METADATA as int, ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as int) ==
            pm_bytes2.subrange(ABSOLUTE_POS_OF_GLOBAL_METADATA as int, ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as int) 
        &&& {
            let metadata_pos = if cdb1.unwrap() { ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_TRUE as int }
                               else { ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as int };
            pm_bytes1.subrange(metadata_pos, metadata_pos + LogMetadata::spec_size_of() + u64::spec_size_of()) ==
            pm_bytes2.subrange(metadata_pos, metadata_pos + LogMetadata::spec_size_of() + u64::spec_size_of())
        }
    }

    pub open spec fn inactive_metadata_types_set(mem: Seq<u8>) -> bool 
    {
        let cdb_pos = ABSOLUTE_POS_OF_LOG_CDB as int;
        let cdb = u64::spec_from_bytes(mem.subrange(cdb_pos, cdb_pos + u64::spec_size_of()));
        let metadata_pos = if cdb == CDB_TRUE { ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as int }
                           else { ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_TRUE as int };
        let metadata =
            LogMetadata::spec_from_bytes(mem.subrange(metadata_pos, metadata_pos + LogMetadata::spec_size_of()));
        let crc_pos = if cdb == CDB_TRUE { ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_FALSE as int }
                      else { ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_TRUE as int };
        let crc = u64::spec_from_bytes(mem.subrange(crc_pos, crc_pos + u64::spec_size_of()));
        &&& u64::bytes_parseable(mem.subrange(cdb_pos, cdb_pos + u64::spec_size_of()))
        &&& LogMetadata::bytes_parseable(mem.subrange(metadata_pos, metadata_pos + LogMetadata::spec_size_of()))
        &&& u64::bytes_parseable(mem.subrange(crc_pos, crc_pos + u64::spec_size_of()))
        &&& cdb == CDB_TRUE || cdb == CDB_FALSE 
        &&& crc == spec_crc_u64(metadata.spec_to_bytes())
    }

    // This invariant says that there are no outstanding writes to the
    // CDB area of persistent memory, and that the committed contents
    // of that area correspond to the given boolean `cdb`.
    pub open spec fn memory_matches_cdb(pm_region_view: PersistentMemoryRegionView, cdb: bool) -> bool
    {
        &&& pm_region_view.no_outstanding_writes_in_range(ABSOLUTE_POS_OF_LOG_CDB as int,
                                                        ABSOLUTE_POS_OF_LOG_CDB + u64::spec_size_of())
        &&& extract_and_parse_log_cdb(pm_region_view.committed()) == Some(cdb)
    }

    pub open spec fn memory_matches_deserialized_cdb(pm_region_view: PersistentMemoryRegionView, cdb: bool) -> bool
    {
        &&& pm_region_view.no_outstanding_writes_in_range(ABSOLUTE_POS_OF_LOG_CDB as int,
                                                        ABSOLUTE_POS_OF_LOG_CDB + u64::spec_size_of())
        &&& deserialize_and_check_log_cdb(pm_region_view.committed()) == Some(cdb)
    }

    // This invariant says that there are no outstanding writes to the
    // activate metadata subregion of the persistent-memory region
    // (i.e., everything but the log area and the log metadata
    // corresponding to `!cdb`). It also says that that metadata is
    // consistent with the log information in `info` and various other
    // in-memory variables given in parameters. The parameters to this
    // function are:
    //
    // `pm_region_view` -- the current view of the persistent memory region
    //
    // `log_id` -- the GUID of the log
    //
    // `cdb` -- the current boolean value of the corruption-detection
    // boolean
    //
    // `info` -- various variables describing information about this
    // log
    pub open spec fn metadata_consistent_with_info(
        pm_region_view: PersistentMemoryRegionView,
        log_id: u128,
        cdb: bool,
        info: LogInfo,
    ) -> bool
    {
        let mem = pm_region_view.committed();
        let global_metadata = deserialize_global_metadata(mem);
        let global_crc = deserialize_global_crc(mem);
        let region_metadata = deserialize_region_metadata(mem);
        let region_crc = deserialize_region_crc(mem);
        let log_metadata = deserialize_log_metadata(mem, cdb);
        let log_crc = deserialize_log_crc(mem, cdb);

        // No outstanding writes to global metadata, region metadata, or the log metadata CDB
        &&& pm_region_view.no_outstanding_writes_in_range(ABSOLUTE_POS_OF_GLOBAL_METADATA as int,
                                                        ABSOLUTE_POS_OF_LOG_CDB as int)
        // Also, no outstanding writes to the log metadata corresponding to the active log metadata CDB
        &&& pm_region_view.no_outstanding_writes_in_range(get_log_metadata_pos(cdb) as int,
                                                        get_log_crc_end(cdb) as int)

        // All the CRCs match
        &&& global_crc == global_metadata.spec_crc()
        &&& region_crc == region_metadata.spec_crc()
        &&& log_crc == log_metadata.spec_crc()

        // Various fields are valid and match the parameters to this function
        &&& global_metadata.program_guid == LOG_PROGRAM_GUID
        &&& global_metadata.version_number == LOG_PROGRAM_VERSION_NUMBER
        &&& global_metadata.length_of_region_metadata == RegionMetadata::spec_size_of()
        &&& region_metadata.region_size == mem.len()
        &&& region_metadata.log_id == log_id
        &&& region_metadata.log_area_len == info.log_area_len
        &&& log_metadata.head == info.head
        &&& log_metadata.log_length == info.log_length

        // The memory region is large enough to hold the entirety of the log area
        &&& mem.len() >= ABSOLUTE_POS_OF_LOG_AREA + info.log_area_len
    }

    // This lemma proves that, if all regions are consistent wrt a new CDB, and then we
    // write and flush that CDB, the regions stay consistent with info.
    //
    pub proof fn lemma_metadata_consistent_with_info_after_cdb_update(
        old_pm_region_view: PersistentMemoryRegionView,
        new_pm_region_view: PersistentMemoryRegionView,
        log_id: u128,
        new_cdb_bytes: Seq<u8>,
        new_cdb: bool,
        info: LogInfo,
    )
        requires
            new_cdb == false ==> new_cdb_bytes == CDB_FALSE.spec_to_bytes(),
            new_cdb == true ==> new_cdb_bytes == CDB_TRUE.spec_to_bytes(),
            new_cdb_bytes.len() == u64::spec_size_of(),
            old_pm_region_view.no_outstanding_writes(),
            new_pm_region_view.no_outstanding_writes(),
            new_pm_region_view =~= old_pm_region_view.write(ABSOLUTE_POS_OF_LOG_CDB as int, new_cdb_bytes).flush(),
            metadata_consistent_with_info(old_pm_region_view, log_id, new_cdb, info),
        ensures
            metadata_consistent_with_info(new_pm_region_view, log_id, new_cdb, info),
    {
        reveal(spec_padding_needed);
        assert(metadata_consistent_with_info(new_pm_region_view, log_id, new_cdb, info)) by {
            let old_mem = old_pm_region_view.committed();
            let new_mem = new_pm_region_view.committed();
            lemma_establish_subrange_equivalence(old_mem, new_mem);
        }
    }

    // This invariant says that the log area of the given
    // persistent-memory region view is consistent with both the log
    // information `info` and the abstract log state `state`. Also,
    // `info` satisfies certain invariant properties and is consistent
    // with `state`.
    //
    // This means three things for every relative log position
    // `pos` and its corresponding persistent-memory byte `pmb`:
    //
    // 1) If `0 <= pos < log_length`, then `pmb` has no outstanding
    // writes and its committed content is the byte in the abstract
    // log at position `pos`. This is critical so that recovery will
    // recover to the right abstract log.
    //
    // 2) If `log_length <= pos < log_plus_pending_length`, then `pmb`
    // may or may not have outstanding writes. But when/if it gets
    // flushed, its content will be the byte in the abstract pending
    // appends at position `pos - log_length`. This is useful so that,
    // when a commit is requested, a flush is all that's needed to
    // durably write the pending appends.
    //
    // 3) If `log_plus_pending_length <= pos < log_area_len`, then
    // `pmb` has no outstanding writes because it's past the pending
    // tail. This is useful so that, if there are further pending
    // appends, they can be written into this part of the log area.
    pub open spec fn info_consistent_with_log_area(
        log_area_view: PersistentMemoryRegionView,
        info: LogInfo,
        state: AbstractLogState,
    ) -> bool
    {
        // `info` satisfies certain invariant properties
        &&& info.log_area_len >= MIN_LOG_AREA_SIZE
        &&& info.log_length <= info.log_plus_pending_length <= info.log_area_len
        &&& info.head_log_area_offset == info.head as int % info.log_area_len as int
        &&& info.head + info.log_plus_pending_length <= u128::MAX

        // `info` and `state` are consistent with each other
        &&& state.log.len() == info.log_length
        &&& state.pending.len() == info.log_plus_pending_length - info.log_length
        &&& state.head == info.head
        &&& state.capacity == info.log_area_len

        // The log area is consistent with `info` and `state`
        &&& forall |pos_relative_to_head: int| {
                let log_area_offset =
                    #[trigger] relative_log_pos_to_log_area_offset(pos_relative_to_head,
                                                                   info.head_log_area_offset as int,
                                                                   info.log_area_len as int);
                let pmb = log_area_view.state[log_area_offset];
                &&& 0 <= pos_relative_to_head < info.log_length ==> {
                      &&& pmb.state_at_last_flush == state.log[pos_relative_to_head]
                      &&& pmb.outstanding_write.is_none()
                   }
                &&& info.log_length <= pos_relative_to_head < info.log_plus_pending_length ==>
                       pmb.flush_byte() == state.pending[pos_relative_to_head - info.log_length]
                &&& info.log_plus_pending_length <= pos_relative_to_head < info.log_area_len ==>
                       pmb.outstanding_write.is_none()
            }
    }

    pub open spec fn info_consistent_with_log_area_in_region(
        pm_region_view: PersistentMemoryRegionView,
        info: LogInfo,
        state: AbstractLogState,
    ) -> bool
    {
        &&& pm_region_view.len() >= ABSOLUTE_POS_OF_LOG_AREA + info.log_area_len
        &&& info_consistent_with_log_area(
               get_subregion_view(pm_region_view, ABSOLUTE_POS_OF_LOG_AREA as nat, info.log_area_len as nat),
               info,
               state
           )
    }

    pub open spec fn metadata_types_set(mem: Seq<u8>) -> bool 
    {
        &&& {
            let metadata_pos = ABSOLUTE_POS_OF_GLOBAL_METADATA as int;
            let crc_pos = ABSOLUTE_POS_OF_GLOBAL_CRC as int;
            let metadata = GlobalMetadata::spec_from_bytes(extract_bytes(mem, metadata_pos as nat,
                                                                         GlobalMetadata::spec_size_of()));
            let crc = u64::spec_from_bytes(extract_bytes(mem, crc_pos as nat, u64::spec_size_of()));
            &&& GlobalMetadata::bytes_parseable(extract_bytes(mem, metadata_pos as nat, GlobalMetadata::spec_size_of()))
            &&& u64::bytes_parseable(extract_bytes(mem, crc_pos as nat, u64::spec_size_of()))
            &&& crc == spec_crc_u64(metadata.spec_to_bytes())
        }
        &&& {
            let metadata_pos = ABSOLUTE_POS_OF_REGION_METADATA as int;
            let crc_pos = ABSOLUTE_POS_OF_REGION_CRC as int;
            let metadata = RegionMetadata::spec_from_bytes(extract_bytes(mem, metadata_pos as nat,
                                                                         RegionMetadata::spec_size_of()));
            let crc = u64::spec_from_bytes(extract_bytes(mem, crc_pos as nat, u64::spec_size_of()));
            &&& RegionMetadata::bytes_parseable(extract_bytes(mem, metadata_pos as nat, RegionMetadata::spec_size_of()))
            &&& u64::bytes_parseable(extract_bytes(mem, crc_pos as nat, u64::spec_size_of()))
            &&& crc == spec_crc_u64(metadata.spec_to_bytes())
        }
        &&& {
            let cdb_pos = ABSOLUTE_POS_OF_LOG_CDB as int;
            let cdb = u64::spec_from_bytes(extract_bytes(mem, cdb_pos as nat, u64::spec_size_of()));
            let metadata_pos = if cdb == CDB_TRUE { ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_TRUE }
                               else { ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE };
            let metadata = LogMetadata::spec_from_bytes(extract_bytes(mem, metadata_pos as nat, LogMetadata::spec_size_of()));
            let crc_pos = if cdb == CDB_TRUE { ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_TRUE }
                          else { ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_FALSE };
            let crc = u64::spec_from_bytes(extract_bytes(mem, crc_pos as nat, u64::spec_size_of()));
            &&& u64::bytes_parseable(extract_bytes(mem, cdb_pos as nat, u64::spec_size_of()))
            &&& cdb == CDB_TRUE || cdb == CDB_FALSE 
            &&& LogMetadata::bytes_parseable(extract_bytes(mem, metadata_pos as nat, LogMetadata::spec_size_of()))
            &&& u64::bytes_parseable(extract_bytes(mem, crc_pos as nat, u64::spec_size_of()))
            &&& crc == spec_crc_u64(metadata.spec_to_bytes())
        }
    }

    pub proof fn lemma_addresses_in_log_area_subregion_correspond_to_relative_log_positions(
        pm_region_view: PersistentMemoryRegionView,
        info: LogInfo
    )
        requires
            pm_region_view.len() == info.log_area_len,
            info.head_log_area_offset < info.log_area_len,
            info.log_area_len > 0,
        ensures
            forall |log_area_offset: int| #![trigger pm_region_view.state[log_area_offset]]
                0 <= log_area_offset < info.log_area_len ==> {
                    let pos_relative_to_head =
                        if log_area_offset >= info.head_log_area_offset {
                            log_area_offset - info.head_log_area_offset
                        }
                        else {
                            log_area_offset - info.head_log_area_offset + info.log_area_len
                        };
                    &&& 0 <= pos_relative_to_head < info.log_area_len
                    &&& log_area_offset ==
                           relative_log_pos_to_log_area_offset(pos_relative_to_head, info.head_log_area_offset as int,
                                                               info.log_area_len as int)
                }
    {
    }

    // This lemma proves that, for any address in the log area of the
    // given persistent memory view, it corresponds to a specific
    // logical position in the abstract log relative to the head. That
    // logical position `pos` satisfies `0 <= pos < log_area_len`.
    //
    // It's useful to call this lemma because it takes facts that
    // trigger `pm_region_view.state[addr]` and turns them into facts
    // that trigger `relative_log_pos_to_log_area_offset`. That's the
    // trigger used in `info_consistent_with_log_area_in_region`.
    pub proof fn lemma_addresses_in_log_area_correspond_to_relative_log_positions(
        pm_region_view: PersistentMemoryRegionView,
        info: LogInfo
    )
        requires
            pm_region_view.len() >= ABSOLUTE_POS_OF_LOG_AREA + info.log_area_len,
            info.head_log_area_offset < info.log_area_len,
            info.log_area_len > 0,
        ensures
            forall |addr: int| #![trigger pm_region_view.state[addr]]
                ABSOLUTE_POS_OF_LOG_AREA <= addr < ABSOLUTE_POS_OF_LOG_AREA + info.log_area_len ==> {
                    let log_area_offset = addr - ABSOLUTE_POS_OF_LOG_AREA;
                    let pos_relative_to_head =
                        if log_area_offset >= info.head_log_area_offset {
                            log_area_offset - info.head_log_area_offset
                        }
                        else {
                            log_area_offset - info.head_log_area_offset + info.log_area_len
                        };
                    &&& 0 <= pos_relative_to_head < info.log_area_len
                    &&& addr == ABSOLUTE_POS_OF_LOG_AREA +
                              relative_log_pos_to_log_area_offset(pos_relative_to_head,
                                                                  info.head_log_area_offset as int,
                                                                  info.log_area_len as int)
                }
    {
    }

    // This lemma proves that, if various invariants hold for the
    // given persistent-memory view `pm_region_view` and abstract log state
    // `state`, and if that view can crash as contents `mem`, then
    // recovery on `mem` will produce `state.drop_pending_appends()`.
    //
    // `pm_region_view` -- the view of this persistent-memory region
    // `mem` -- a possible memory contents that `pm_region_view` can crash as
    // `log_id` -- the ID of the log
    // `cdb` -- the current value of the corruption-detecting boolean
    // `info` -- the log information
    // `state` -- the abstract log state
    //

    proof fn lemma_invariants_imply_crash_recover_for_one_log(
        pm_region_view: PersistentMemoryRegionView,
        mem: Seq<u8>,
        log_id: u128,
        cdb: bool,
        info: LogInfo,
        state: AbstractLogState,
    )
        requires
            pm_region_view.can_crash_as(mem),
            metadata_consistent_with_info(pm_region_view, log_id, cdb, info),
            info_consistent_with_log_area_in_region(pm_region_view, info, state),
        ensures
            recover_given_cdb(mem, log_id, cdb) == Some(state.drop_pending_appends())
    {
        reveal(spec_padding_needed);

        // For the metadata, we observe that:
        //
        // (1) there are no outstanding writes, so the crashed-into
        //     state `mem` must match the committed state
        //     `pm_region_view.committed()`, and
        // (2) wherever the crashed-into state matches the committed
        //     state on a per-byte basis, any `extract_bytes` results
        //     will also match.
        //
        // Therefore, since the metadata in
        // `pm_region_view.committed()` matches `state` (per the
        // invariants), the metadata in `mem` must also match `state`.

        lemma_wherever_no_outstanding_writes_persistent_memory_view_can_only_crash_as_committed(pm_region_view);
        lemma_establish_subrange_equivalence(mem, pm_region_view.committed());

        // The tricky part is showing that the result of `extract_log` will produce the desired result.
        // Use `=~=` to ask Z3 to prove this equivalence by proving it holds on each byte.

        let log_view = get_subregion_view(pm_region_view, ABSOLUTE_POS_OF_LOG_AREA as nat, info.log_area_len as nat);
        lemma_wherever_no_outstanding_writes_persistent_memory_view_can_only_crash_as_committed(log_view);
        assert(recover_log_from_log_area_given_metadata(log_view.committed(), info.head as int, info.log_length as int)
               =~= Some(state.drop_pending_appends()));
        assert(recover_log(mem, info.log_area_len as int, info.head as int, info.log_length as int)
               =~= Some(state.drop_pending_appends()));
    }

    // This lemma proves that, if various invariants hold for the
    // given persistent-memory region view `pm_region_view` and
    // abstract log state `state`, and if that view can crash as
    // contents `mem`, then recovery on `mem` will produce
    // `state.drop_pending_appends()`.
    //
    // `pm_region_view` -- the persistent memory region view
    // `mem` -- a possible memory contents that `pm_region_view` can crash as
    // `log_id` -- the ID of the log
    // `cdb` -- the current value of the corruption-detecting boolean
    // `info` -- the log information
    // `state` -- the abstract multilog state
    //
    proof fn lemma_invariants_imply_crash_recover(
        pm_region_view: PersistentMemoryRegionView,
        mem: Seq<u8>,
        log_id: u128,
        cdb: bool,
        info: LogInfo,
        state: AbstractLogState,
    )
        requires
            pm_region_view.can_crash_as(mem),
            memory_matches_deserialized_cdb(pm_region_view, cdb),
            metadata_consistent_with_info(pm_region_view, log_id, cdb, info),
            info_consistent_with_log_area_in_region(pm_region_view, info, state),
            metadata_types_set(pm_region_view.committed()),
        ensures
            recover_cdb(mem) == Some(cdb),
            recover_state(mem, log_id) == Some(state.drop_pending_appends()),
            metadata_types_set(mem),
    {
        reveal(spec_padding_needed);

        // For the CDB, we observe that:
        //
        // (1) there are no outstanding writes, so the crashed-into
        // state `mem` must match the committed state
        // `pm_region_view.committed()`, and
        //
        // (2) wherever the crashed-into state matches the committed
        // state on a per-byte basis, any `extract_bytes` results will
        // also match.
        //
        // Therefore, since the metadata in `pm_region_view.committed()`
        // matches `cdb` (per the invariants), the metadata in
        // `mem` must also match `cdb`.

        assert (recover_cdb(mem) == Some(cdb)) by {
            lemma_wherever_no_outstanding_writes_persistent_memory_view_can_only_crash_as_committed(pm_region_view);
            lemma_establish_subrange_equivalence(mem, pm_region_view.committed());
        }

        // Use `lemma_invariants_imply_crash_recover_for_one_log` on
        // each region to establish that recovery works on all the
        // regions.

        assert(recover_given_cdb(mem, log_id, cdb) == Some(state.drop_pending_appends())) by {
            lemma_invariants_imply_crash_recover_for_one_log(pm_region_view, mem, log_id, cdb, info, state);
        }

        // Get Z3 to see the equivalence of the recovery
        // result and the desired abstract state by asking it (with
        // `=~=`) to prove that they're piecewise equivalent.

        assert(recover_state(mem, log_id) =~= Some(state.drop_pending_appends()));

        // Finally, invoke the lemma that proves that metadata types 
        // are still set in crash states

        lemma_metadata_set_after_crash(pm_region_view, cdb);
    }

    // This exported lemma proves that, if various invariants hold for
    // the given persistent memory region view `pm_region_view` and
    // abstract log state `state`, then for any contents `mem`
    // the view can recover into, recovery on `mem` will produce
    // `state.drop_pending_appends()`.
    //
    // `pm_region_view` -- the persistent memory region view
    // `log_id` -- the ID of the log
    // `cdb` -- the current value of the corruption-detecting boolean
    // `info` -- the log information
    // `state` -- the abstract log state
    pub proof fn lemma_invariants_imply_crash_recover_forall(
        pm_region_view: PersistentMemoryRegionView,
        log_id: u128,
        cdb: bool,
        info: LogInfo,
        state: AbstractLogState,
    )
        requires
            memory_matches_deserialized_cdb(pm_region_view, cdb),
            metadata_consistent_with_info(pm_region_view, log_id, cdb, info),
            info_consistent_with_log_area_in_region(pm_region_view, info, state),
            metadata_types_set(pm_region_view.committed()),
        ensures
            forall |mem| #[trigger] pm_region_view.can_crash_as(mem) ==> {
                &&& recover_cdb(mem) == Some(cdb)
                &&& recover_state(mem, log_id) == Some(state.drop_pending_appends())
                &&& metadata_types_set(mem)
            }
    {
        assert forall |mem| #[trigger] pm_region_view.can_crash_as(mem) implies {
                   &&& recover_cdb(mem) == Some(cdb)
                   &&& recover_state(mem, log_id) == Some(state.drop_pending_appends())
                   &&& metadata_types_set(mem)
               } by
        {
            lemma_invariants_imply_crash_recover(pm_region_view, mem, log_id, cdb, info, state);
        }
    }

    // This lemma establishes that, if one updates the inactive
    // log metadata in a region, this will maintain various
    // invariants. The "inactive" log metadata is the
    // metadata corresponding to the negation of the current
    // corruption-detecting boolean.
    //
    // `pm_region_view` -- the persistent memory region view
    // `log_id` -- the ID of the log
    // `cdb` -- the current value of the corruption-detecting boolean
    // `info` -- the log information
    // `state` -- the abstract log state
    // `bytes_to_write` -- bytes to be written to the inactive log metadata area
    pub proof fn lemma_updating_inactive_metadata_maintains_invariants(
        pm_region_view: PersistentMemoryRegionView,
        log_id: u128,
        cdb: bool,
        info: LogInfo,
        state: AbstractLogState,
        bytes_to_write: Seq<u8>,
    )
        requires
            memory_matches_deserialized_cdb(pm_region_view, cdb),
            metadata_consistent_with_info(pm_region_view, log_id, cdb, info),
            info_consistent_with_log_area_in_region(pm_region_view, info, state),
            bytes_to_write.len() == LogMetadata::spec_size_of(),
            metadata_types_set(pm_region_view.committed())
       ensures
            ({
                let pm_region_view2 = pm_region_view.write(get_log_metadata_pos(!cdb) as int, bytes_to_write);
                &&& memory_matches_deserialized_cdb(pm_region_view2, cdb)
                &&& metadata_consistent_with_info(pm_region_view2, log_id, cdb, info)
                &&& info_consistent_with_log_area_in_region(pm_region_view2, info, state)
                &&& metadata_types_set(pm_region_view2.committed())
            })
    {
        reveal(spec_padding_needed);

        let pm_region_view2 = pm_region_view.write(get_log_metadata_pos(!cdb) as int, bytes_to_write);

        assert(memory_matches_deserialized_cdb(pm_region_view2, cdb)) by {
            assert(extract_log_cdb(pm_region_view2.committed()) =~=
                   extract_log_cdb(pm_region_view.committed()));
        }

        // To show that all the metadata still matches even after the
        // write, observe that everywhere the bytes match, any call to
        // `extract_bytes` will also match.

        lemma_establish_subrange_equivalence(pm_region_view.committed(), pm_region_view2.committed());

        let mem = pm_region_view.committed();
        let global_metadata = deserialize_global_metadata(mem);
        let global_crc = deserialize_global_crc(mem);
        let region_metadata = deserialize_region_metadata(mem);
        let region_crc = deserialize_region_crc(mem);
        let log_metadata = deserialize_log_metadata(mem, cdb);
        let log_crc = deserialize_log_crc(mem, cdb);

        let mem2 = pm_region_view2.committed();
        let global_metadata2 = deserialize_global_metadata(mem2);
        let global_crc2 = deserialize_global_crc(mem2);
        let region_metadata2 = deserialize_region_metadata(mem2);
        let region_crc2 = deserialize_region_crc(mem2);
        let log_metadata2 = deserialize_log_metadata(mem2, cdb);
        let log_crc2 = deserialize_log_crc(mem2, cdb);

        let global_metadata_bytes1 = extract_bytes(mem, ABSOLUTE_POS_OF_GLOBAL_METADATA as nat, GlobalMetadata::spec_size_of() as nat);
        let global_metadata_bytes2 = extract_bytes(mem2, ABSOLUTE_POS_OF_GLOBAL_METADATA as nat, GlobalMetadata::spec_size_of() as nat);
    
        assert(metadata_consistent_with_info(pm_region_view2, log_id, cdb, info)) by {
            lemma_establish_subrange_equivalence(pm_region_view.committed(), pm_region_view2.committed());
        }

        assert(mem.subrange(ABSOLUTE_POS_OF_GLOBAL_METADATA as int, ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as int) == 
            (mem2.subrange(ABSOLUTE_POS_OF_GLOBAL_METADATA as int, ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as int)));
        if cdb {
            assert(extract_bytes(mem, ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_TRUE as nat, LogMetadata::spec_size_of() + u64::spec_size_of()) == 
                extract_bytes(mem2, ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_TRUE as nat, LogMetadata::spec_size_of() + u64::spec_size_of()));
        } else {
            assert(extract_bytes(mem, ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as nat, LogMetadata::spec_size_of() + u64::spec_size_of()) ==
                extract_bytes(mem2, ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as nat, LogMetadata::spec_size_of() + u64::spec_size_of()));
        }
        assert(active_metadata_bytes_are_equal(mem, mem2));
        lemma_metadata_matches_implies_metadata_types_set(pm_region_view, pm_region_view2, cdb);
    }

    // This lemma establishes that, if one updates the inactive
    // log metadata in a region, this will maintain various
    // invariants. The "inactive" log metadata is the
    // metadata corresponding to the negation of the current
    // corruption-detecting boolean.
    //
    // `pm_region_view` -- the persistent memory region view
    // `log_id` -- the ID of the log
    // `cdb` -- the current value of the corruption-detecting boolean
    // `info` -- the log information
    // `state` -- the abstract log state
    // `bytes_to_write` -- bytes to be written to the inactive log metadata area
    pub proof fn lemma_updating_inactive_crc_maintains_invariants(
        pm_region_view: PersistentMemoryRegionView,
        log_id: u128,
        cdb: bool,
        info: LogInfo,
        state: AbstractLogState,
        bytes_to_write: Seq<u8>,
    )
        requires
            memory_matches_deserialized_cdb(pm_region_view, cdb),
            metadata_consistent_with_info(pm_region_view, log_id, cdb, info),
            info_consistent_with_log_area_in_region(pm_region_view, info, state),
            bytes_to_write.len() == u64::spec_size_of(),
            metadata_types_set(pm_region_view.committed()),
        ensures
            ({
                let pm_region_view2 = pm_region_view.write(
                    get_log_metadata_pos(!cdb) + LogMetadata::spec_size_of(),
                    bytes_to_write
                );
                &&& memory_matches_deserialized_cdb(pm_region_view2, cdb)
                &&& metadata_consistent_with_info(pm_region_view2, log_id, cdb, info)
                &&& info_consistent_with_log_area_in_region(pm_region_view2, info, state)
                &&& metadata_types_set(pm_region_view2.flush().committed())
            })
    {
        reveal(spec_padding_needed);
        let pm_region_view2 = pm_region_view.write(
            get_log_metadata_pos(!cdb) + LogMetadata::spec_size_of(),
            bytes_to_write
        );

        assert(memory_matches_deserialized_cdb(pm_region_view2, cdb)) by {
            assert(extract_log_cdb(pm_region_view2.committed()) =~=
                   extract_log_cdb(pm_region_view.committed()));
        }

        let mem = pm_region_view.committed();
        let mem2 = pm_region_view2.flush().committed();

        assert(extract_bytes(mem, ABSOLUTE_POS_OF_LOG_CDB as nat, u64::spec_size_of()) ==
               extract_bytes(mem2, ABSOLUTE_POS_OF_LOG_CDB as nat, u64::spec_size_of()));

        assert(mem.subrange(ABSOLUTE_POS_OF_GLOBAL_METADATA as int, ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as int) ==
                mem2.subrange(ABSOLUTE_POS_OF_GLOBAL_METADATA as int, ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as int));
        if cdb {
            assert(extract_bytes(mem, ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_TRUE as nat, LogMetadata::spec_size_of() + u64::spec_size_of()) ==
                extract_bytes(mem2, ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_TRUE as nat, LogMetadata::spec_size_of() + u64::spec_size_of()));
        } else {
            assert(extract_bytes(mem, ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as nat, LogMetadata::spec_size_of() + u64::spec_size_of()) ==
                extract_bytes(mem2, ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as nat, LogMetadata::spec_size_of() + u64::spec_size_of()));
        }

        // To show that all the metadata still matches even after the
        // write, observe that everywhere the bytes match, any call to
        // `extract_bytes` will also match.

        assert(metadata_consistent_with_info(pm_region_view2, log_id, cdb, info)) by {
            lemma_establish_subrange_equivalence(pm_region_view.committed(), pm_region_view2.committed());
        }

        lemma_metadata_matches_implies_metadata_types_set(pm_region_view, pm_region_view2.flush(), cdb);
    }

    // This lemma establishes that, if one flushes persistent memory,
    // this will maintain various invariants.
    //
    // `pm_region_view` -- the persistent memory region view
    // `log_id` -- the ID of the log
    // `cdb` -- the current value of the corruption-detecting boolean
    // `info` -- the log information
    // `state` -- the abstract log state
    pub proof fn lemma_flushing_metadata_maintains_invariants(
        pm_region_view: PersistentMemoryRegionView,
        log_id: u128,
        cdb: bool,
        info: LogInfo,
        state: AbstractLogState,
    )
        requires
            memory_matches_deserialized_cdb(pm_region_view, cdb),
            metadata_consistent_with_info(pm_region_view,  log_id, cdb, info),
            info_consistent_with_log_area_in_region(pm_region_view, info, state),
            metadata_types_set(pm_region_view.committed()),
       ensures
            ({
                let pm_region_view2 = pm_region_view.flush();
                &&& memory_matches_deserialized_cdb(pm_region_view2, cdb)
                &&& metadata_consistent_with_info(pm_region_view2, log_id, cdb, info)
                &&& info_consistent_with_log_area_in_region(pm_region_view2, info, state)
                &&& metadata_types_set(pm_region_view2.committed())
            })
    {
        reveal(spec_padding_needed);
        let pm_region_view2 = pm_region_view.flush();

        assert(memory_matches_deserialized_cdb(pm_region_view2, cdb)) by {
            assert(extract_log_cdb(pm_region_view2.committed()) =~=
                   extract_log_cdb(pm_region_view.committed()));
        }

        // To show that all the metadata still matches even after the
        // flush, observe that everywhere the bytes match, any call to
        // `extract_bytes` will also match.

        assert(metadata_consistent_with_info(pm_region_view2, log_id, cdb, info)) by {
            lemma_establish_subrange_equivalence(pm_region_view.committed(), pm_region_view2.committed());
        }

        // Prove that the bytes in the active metadata are unchanged after the flush, so 
        // the metadata types are still set.
        
        assert(active_metadata_is_equal(pm_region_view, pm_region_view2)) by {
            let mem1 = pm_region_view.committed();
            let mem2 = pm_region_view2.committed();
            let log_metadata_pos = get_log_metadata_pos(cdb);

            assert(deserialize_and_check_log_cdb(mem1) == deserialize_and_check_log_cdb(mem2));
            assert(mem1.subrange(ABSOLUTE_POS_OF_GLOBAL_METADATA as int, ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as int) == 
                mem2.subrange(ABSOLUTE_POS_OF_GLOBAL_METADATA as int, ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as int));
            assert(extract_bytes(mem1, log_metadata_pos as nat, LogMetadata::spec_size_of() + u64::spec_size_of()) == 
                extract_bytes(mem2, log_metadata_pos as nat, LogMetadata::spec_size_of() + u64::spec_size_of()));
        }
        lemma_metadata_matches_implies_metadata_types_set(pm_region_view, pm_region_view2, cdb);
    }

    // This predicate describes whether a given log area offset is
    // unreachable during recovery (because it's beyond the tail).
    //
    // Its parameters are:
    // `head_log_area_offset` -- the the log offset where the log head is
    // `log_area_len` -- the length of the log area
    // `log_length` -- the length of the abstract log
    // `log_area_offset` -- the log area offet being asked about
    pub open spec fn log_area_offset_unreachable_during_recovery(
        head_log_area_offset: int,
        log_area_len: int,
        log_length: int,
        log_area_offset: int,
    ) -> bool
    {
        log_area_offset_to_relative_log_pos(log_area_offset, head_log_area_offset, log_area_len) >= log_length
    }

    // This lemma establishes that if:
    //
    // 1) two views `v1` and `v2` only differ in unreachable parts of
    // the log area (one that satisfy
    // `log_area_offset_unreachable_during_recovery`),
    //
    // 2) view `v1` satisfies certain invariant properties,
    //
    // 3) view `v2` can crash into state `crash_state`,
    //
    // then `crash_state` recovers to the same abstract state as
    // `v1.committed()`. This is useful to know for the following
    // reason. `v1` can obviously crash as `v1.committed()`. So, if we
    // know that all possible crash states of `v1` recover to a valid
    // state then we know `crash_state` recovers to a valid state.
    //
    // The parameters to this function are:
    //
    // `v1` and `v2` -- the two views
    // `crash_state` -- the state that `v2` can crash into
    // `log_id` -- the ID of the log
    // `cdb` -- the current value of the corruption-detecting boolean
    // `info` -- the log information
    // `state` -- the abstract log state
    // `is_writable_absolute_addr` -- a spec predicate describing
    // which absolute addresses in the log area may differ between
    // `v1` and `v2`.
    pub proof fn lemma_if_view_differs_only_in_log_area_parts_not_accessed_by_recovery_then_recover_state_matches(
        v1: PersistentMemoryRegionView,
        v2: PersistentMemoryRegionView,
        crash_state: Seq<u8>,
        log_id: u128,
        cdb: bool,
        info: LogInfo,
        state: AbstractLogState,
        is_writable_absolute_addr: spec_fn(int) -> bool,
    )
        requires
            no_outstanding_writes_to_metadata(v1),
            memory_matches_deserialized_cdb(v1, cdb),
            metadata_consistent_with_info(v1, log_id, cdb, info),
            info_consistent_with_log_area_in_region(v1, info, state),
            ABSOLUTE_POS_OF_LOG_AREA + info.log_area_len <= v1.len(),
            v2.can_crash_as(crash_state),
            v1.len() == v2.len(),
            forall |addr: int| #[trigger] is_writable_absolute_addr(addr) <==> 
                  log_area_offset_unreachable_during_recovery(info.head_log_area_offset as int,
                                                              info.log_area_len as int,
                                                              info.log_length as int,
                                                              addr - ABSOLUTE_POS_OF_LOG_AREA),
            views_differ_only_where_subregion_allows(v1, v2, ABSOLUTE_POS_OF_LOG_AREA as nat,
                                                     info.log_area_len as nat, is_writable_absolute_addr),
        ensures
            v1.can_crash_as(v1.committed()),
            recover_state(crash_state, log_id) == recover_state(v1.committed(), log_id),
    {
        reveal(spec_padding_needed);
        lemma_wherever_no_outstanding_writes_persistent_memory_view_can_only_crash_as_committed(v2);
        lemma_establish_subrange_equivalence(crash_state, v1.committed());
        assert(recover_state(crash_state, log_id) =~= recover_state(v1.committed(), log_id));
    }

    // This lemma proves that if the log metadata has been properly set up and there are no outstanding writes to 
    // metadata, then the metadata_types_set invariant holds after any crash. This is useful when proving the invariant
    // after an update that does not touch metadata.
    pub proof fn lemma_metadata_set_after_crash(
        pm_region_view: PersistentMemoryRegionView,
        cdb: bool
    )
        requires 
            no_outstanding_writes_to_active_metadata(pm_region_view, cdb),
            metadata_types_set(pm_region_view.committed()),
            memory_matches_deserialized_cdb(pm_region_view, cdb),
        ensures 
            forall |s| #![auto] {
                &&& pm_region_view.can_crash_as(s) 
                &&& 0 <= ABSOLUTE_POS_OF_GLOBAL_METADATA < ABSOLUTE_POS_OF_LOG_AREA < s.len()
            } ==> metadata_types_set(s),
    {
        reveal(spec_padding_needed);

        let pm_bytes = pm_region_view.committed();
        assert(cdb == deserialize_and_check_log_cdb(pm_bytes).unwrap());

        lemma_wherever_no_outstanding_writes_persistent_memory_view_can_only_crash_as_committed(pm_region_view);

        assert forall |s| {
            &&& pm_region_view.can_crash_as(s) 
            &&& 0 <= ABSOLUTE_POS_OF_GLOBAL_METADATA < ABSOLUTE_POS_OF_LOG_AREA < s.len()
        } implies {
            let s_cdb = deserialize_and_check_log_cdb(s).unwrap();
            &&& deserialize_global_metadata(s) == deserialize_global_metadata(pm_bytes)
            &&& deserialize_global_crc(s) == deserialize_global_crc(pm_bytes)
            &&& deserialize_region_metadata(s) == deserialize_region_metadata(pm_bytes)
            &&& deserialize_region_crc(s) == deserialize_region_crc(pm_bytes)
            &&& s_cdb == cdb 
            &&& if s_cdb {
                   &&& deserialize_log_metadata(s, true) == deserialize_log_metadata(pm_bytes, true)
                   &&& deserialize_log_crc(s, true) == deserialize_log_crc(pm_bytes, true)
               }
               else {
                   &&& deserialize_log_metadata(s, false) == deserialize_log_metadata(pm_bytes, false)
                   &&& deserialize_log_crc(s, false) == deserialize_log_crc(pm_bytes, false)
               }
        } by {
            lemma_establish_subrange_equivalence(s, pm_region_view.committed());
        }

        assert forall |s| #![auto] {
            &&& pm_region_view.can_crash_as(s) 
            &&& 0 <= ABSOLUTE_POS_OF_GLOBAL_METADATA < ABSOLUTE_POS_OF_LOG_AREA < s.len()
        } implies metadata_types_set(s) by {
            lemma_establish_subrange_equivalence(s, pm_region_view.committed());
        }
    }

    // This lemma proves that if we two PM states have the same bytes in the log header and no outstanding writes in that region,
    // and one of the states has metadata types set, then the other also has metadata types set. This is useful for proving 
    // that the metadata types invariant holds when appending to the log.
    pub proof fn lemma_metadata_matches_implies_metadata_types_set(
        pm1: PersistentMemoryRegionView,
        pm2: PersistentMemoryRegionView,
        cdb: bool
    )
        requires 
            no_outstanding_writes_to_active_metadata(pm1, cdb),
            no_outstanding_writes_to_active_metadata(pm2, cdb),
            metadata_types_set(pm1.committed()),
            memory_matches_deserialized_cdb(pm1, cdb),
            0 < ABSOLUTE_POS_OF_LOG_AREA < pm1.committed().len(),
            0 < ABSOLUTE_POS_OF_LOG_AREA < pm2.committed().len(),
            active_metadata_is_equal(pm1, pm2),
            pm1.len() == pm2.len()
        ensures 
            metadata_types_set(pm2.committed())
    {
        lemma_active_metadata_bytes_equal_implies_metadata_types_set(pm1.committed(), pm2.committed(), cdb);
    }

    // This lemma proves that if two sequences have equal active metadata bytes and one has its metadata types set,
    // then the other sequence also has its metadata types set.
    pub proof fn lemma_active_metadata_bytes_equal_implies_metadata_types_set(
        mem1: Seq<u8>,
        mem2: Seq<u8>,
        cdb: bool
    )
        requires 
            ABSOLUTE_POS_OF_LOG_AREA <= mem1.len(),
            ABSOLUTE_POS_OF_LOG_AREA <= mem2.len(),
            active_metadata_bytes_are_equal(mem1, mem2),
            ({
                let cdb1 = deserialize_and_check_log_cdb(mem1);
                let cdb2 = deserialize_and_check_log_cdb(mem2);
                let log_metadata_pos = get_log_metadata_pos(cdb);
                &&& cdb1 is Some 
                &&& cdb2 is Some 
                &&& cdb ==> cdb1.unwrap() && cdb2.unwrap()
                &&& !cdb ==> !cdb1.unwrap() && !cdb2.unwrap()
            }),
            metadata_types_set(mem1)
        ensures 
            metadata_types_set(mem2),
    {
        reveal(spec_padding_needed);

        lemma_establish_subrange_equivalence(mem1, mem2);

        // This lemma automatically establishes the relationship between subranges of subranges from the same sequence, 
        // so knowing that the assertions below cover subranges of larger, equal subranges is enough to establish equality
        // (but we have to assert it explicitly to hit the triggers)
        lemma_auto_smaller_range_of_seq_is_subrange(mem1);

        // First, establish that the immutable parts and the CDB are the same between both byte sequences.
        let mem1_without_log_metadata = mem1.subrange(ABSOLUTE_POS_OF_GLOBAL_METADATA as int, ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as int);
        let mem2_without_log_metadata = mem2.subrange(ABSOLUTE_POS_OF_GLOBAL_METADATA as int, ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as int);
        assert(extract_bytes(mem1, ABSOLUTE_POS_OF_GLOBAL_METADATA as nat, GlobalMetadata::spec_size_of()) == 
            extract_bytes(mem2, ABSOLUTE_POS_OF_GLOBAL_METADATA as nat, GlobalMetadata::spec_size_of()));
        assert(extract_bytes(mem1, ABSOLUTE_POS_OF_GLOBAL_CRC as nat, u64::spec_size_of()) == 
            extract_bytes(mem2, ABSOLUTE_POS_OF_GLOBAL_CRC as nat, u64::spec_size_of()));
        assert(extract_bytes(mem1, ABSOLUTE_POS_OF_REGION_METADATA as nat, RegionMetadata::spec_size_of()) == 
            extract_bytes(mem2, ABSOLUTE_POS_OF_REGION_METADATA as nat, RegionMetadata::spec_size_of()));
        assert(extract_bytes(mem1, ABSOLUTE_POS_OF_REGION_CRC as nat, u64::spec_size_of()) == 
            extract_bytes(mem2, ABSOLUTE_POS_OF_REGION_CRC as nat, u64::spec_size_of()));
        assert(extract_bytes(mem1, ABSOLUTE_POS_OF_LOG_CDB as nat, u64::spec_size_of()) == 
            extract_bytes(mem2, ABSOLUTE_POS_OF_LOG_CDB as nat, u64::spec_size_of()));

        // Next, establish that the types are set in the active metadata
        let log_metadata_pos = get_log_metadata_pos(cdb);
        assert(extract_bytes(mem1, log_metadata_pos as nat, LogMetadata::spec_size_of()) == 
            extract_bytes(mem2, log_metadata_pos as nat, LogMetadata::spec_size_of()));
        assert(extract_bytes(mem1, log_metadata_pos as nat + LogMetadata::spec_size_of(), u64::spec_size_of()) ==
            extract_bytes(mem2, log_metadata_pos as nat + LogMetadata::spec_size_of(), u64::spec_size_of()));
    }

    pub proof fn lemma_auto_smaller_range_of_seq_is_subrange(mem1: Seq<u8>)
        ensures 
            forall |i: int, j, k: int, l: int| 0 <= i <= k <= l <= j <= mem1.len() ==> mem1.subrange(i, j).subrange(k - i, l - i) == mem1.subrange(k, l) 
    {
        assert forall |i: int, j, k: int, l: int| 0 <= i <= k <= l <= j <= mem1.len() implies mem1.subrange(i, j).subrange(k - i, l - i) == mem1.subrange(k, l) by {
            lemma_smaller_range_of_seq_is_subrange(mem1, i, j, k, l);
        }
    }

    pub proof fn lemma_smaller_range_of_seq_is_subrange(mem1: Seq<u8>, i: int, j: int, k: int, l: int)
        requires 
            0 <= i <= k <= l <= j <= mem1.len()
        ensures 
            mem1.subrange(i, j).subrange(k - i, l - i) == mem1.subrange(k, l) 
    {
        assert(mem1.subrange(k, l) == mem1.subrange(i + k - i, i + l - i));
        assert(mem1.subrange(i, j).subrange(k - i, l - i) == mem1.subrange(i + k - i, i + l - i));
    }
      
    pub proof fn lemma_header_bytes_equal_implies_active_metadata_bytes_equal(mem1: Seq<u8>, mem2: Seq<u8>)
        requires 
            ABSOLUTE_POS_OF_LOG_AREA <= mem1.len(),
            ABSOLUTE_POS_OF_LOG_AREA <= mem2.len(),
            mem1.subrange(ABSOLUTE_POS_OF_GLOBAL_METADATA as int, ABSOLUTE_POS_OF_LOG_AREA as int) =~= 
                mem2.subrange(ABSOLUTE_POS_OF_GLOBAL_METADATA as int, ABSOLUTE_POS_OF_LOG_AREA as int),
            deserialize_and_check_log_cdb(mem1) is Some,
        ensures 
            active_metadata_bytes_are_equal(mem1, mem2)
    {
        reveal(spec_padding_needed);
        lemma_establish_subrange_equivalence(mem1, mem2);

        lemma_auto_smaller_range_of_seq_is_subrange(mem1);

        let cdb = deserialize_and_check_log_cdb(mem1).unwrap();
        let log_metadata_pos = get_log_metadata_pos(cdb);

        assert(mem1.subrange(ABSOLUTE_POS_OF_GLOBAL_METADATA as int, ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as int) ==
            mem2.subrange(ABSOLUTE_POS_OF_GLOBAL_METADATA as int, ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as int) );
        assert(mem1.subrange(log_metadata_pos as int, log_metadata_pos + LogMetadata::spec_size_of() + u64::spec_size_of()) == 
            mem2.subrange(log_metadata_pos as int, log_metadata_pos + LogMetadata::spec_size_of() + u64::spec_size_of()));
    }

    pub proof fn lemma_metadata_types_set_after_cdb_update(
        old_pm_region_view: PersistentMemoryRegionView,
        new_pm_region_view: PersistentMemoryRegionView,
        log_id: u128,
        new_cdb_bytes: Seq<u8>,
        old_cdb: bool,
    )
        requires 
            old_pm_region_view.no_outstanding_writes(),
            new_pm_region_view.no_outstanding_writes(),
            old_pm_region_view.len() >= ABSOLUTE_POS_OF_LOG_AREA,
            old_pm_region_view.len() == new_pm_region_view.len(),
            new_cdb_bytes == CDB_FALSE.spec_to_bytes() || new_cdb_bytes == CDB_TRUE.spec_to_bytes(),
            old_cdb ==> new_cdb_bytes == CDB_FALSE.spec_to_bytes(),
            !old_cdb ==> new_cdb_bytes == CDB_TRUE.spec_to_bytes(),
            new_pm_region_view =~= old_pm_region_view.write(ABSOLUTE_POS_OF_LOG_CDB as int, new_cdb_bytes).flush(),
            metadata_types_set(old_pm_region_view.committed()),
            inactive_metadata_types_set(old_pm_region_view.committed())
        ensures 
            metadata_types_set(new_pm_region_view.committed())
    {
        broadcast use pmcopy_axioms;
        reveal(spec_padding_needed);

        let old_mem = old_pm_region_view.committed();
        let new_mem = new_pm_region_view.committed();
        lemma_auto_smaller_range_of_seq_is_subrange(old_mem);
        lemma_auto_smaller_range_of_seq_is_subrange(new_mem);
        
        // Immutable metadata has not changed
        assert(old_mem.subrange(ABSOLUTE_POS_OF_GLOBAL_METADATA as int, ABSOLUTE_POS_OF_LOG_CDB as int) =~=
            new_mem.subrange(ABSOLUTE_POS_OF_GLOBAL_METADATA as int, ABSOLUTE_POS_OF_LOG_CDB as int));

        // We updated the CDB -- its type is still set, since new_cdb_bytes corresponds to a serialization of a valid CDB value
        assert(extract_bytes(new_mem, ABSOLUTE_POS_OF_LOG_CDB as nat, u64::spec_size_of()) == new_cdb_bytes);

        let new_cdb = deserialize_and_check_log_cdb(new_mem).unwrap();
        let active_metadata_pos = get_log_metadata_pos(new_cdb);
        // The bytes in the new active position are the same in both byte sequences, and they had their metadata types set in the old view,
        // so types are also set in the new view, and the postcondition holds.
        assert(extract_bytes(new_mem, active_metadata_pos as nat, LogMetadata::spec_size_of() + u64::spec_size_of()) == 
            extract_bytes(old_mem, active_metadata_pos as nat, LogMetadata::spec_size_of() + u64::spec_size_of()));
    }
}
