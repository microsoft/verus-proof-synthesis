//! This file contains lemmas about tentatively appending to a
//! multilog.
//!
//! The code in this file is verified and untrusted (as indicated by
//! the `_v.rs` suffix), so you don't have to read it to be confident
//! of the system's correctness.

use crate::multilog::inv_v::*;
use crate::multilog::layout_v::*;
use crate::multilog::multilogimpl_v::LogInfo;
use crate::multilog::multilogspec_t::AbstractMultiLogState;
use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemspec_t::PersistentMemoryRegionsView;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

verus! {

    // This lemma establishes useful facts about performing a
    // contiguous write to effect a tentative append:
    //
    // 1) It's permitted because a crash after the write is initiated
    //    doesn't affect the post-recovery abstract state.
    //
    // 2) It maintains invariants, if `infos` and `state` are updated
    //    in a certain way.
    //
    // Parameters:
    //
    // `pm_regions_view` -- the view of the persistent memory regions
    // before the write
    //
    // `multilog_id` -- the ID of the multilog stored on that memory
    //
    // `num_logs` -- the number of logs in the multilog
    //
    // `which_log` -- which log among the logs is being tentatively
    // appended to
    //
    // `bytes_to_append` -- what bytes are being tentatively appended
    //
    // `cdb` -- the current corruption-detecting boolean value
    //
    // `prev_infos` -- the pre-append `infos` value
    //
    // `prev_state` -- the pre-append abstract state
    pub proof fn lemma_tentatively_append(
        pm_regions_view: PersistentMemoryRegionsView,
        multilog_id: u128,
        num_logs: u32,
        which_log: u32,
        bytes_to_append: Seq<u8>,
        cdb: bool,
        prev_infos: Seq<LogInfo>,
        prev_state: AbstractMultiLogState,
    )
        requires
            log_index_trigger(which_log as int),
            which_log < num_logs,
            memory_matches_deserialized_cdb(pm_regions_view, cdb),
            each_metadata_consistent_with_info(pm_regions_view, multilog_id, num_logs, cdb, prev_infos),
            each_info_consistent_with_log_area(pm_regions_view, num_logs, prev_infos, prev_state),
            no_outstanding_writes_to_metadata(pm_regions_view),
            metadata_types_set(pm_regions_view.committed()),
            forall |i: int| #[trigger] log_index_trigger(i) && 0 <= i < pm_regions_view.len() ==>
                ABSOLUTE_POS_OF_LOG_AREA < pm_regions_view[i].len(),
            ({
                let prev_info = prev_infos[which_log as int];
                let log_area_len = prev_info.log_area_len;
                let num_bytes = bytes_to_append.len();
                let max_len_without_wrapping = log_area_len -
                    relative_log_pos_to_log_area_offset(prev_info.log_plus_pending_length as int,
                                                        prev_info.head_log_area_offset as int, log_area_len as int);
                &&& 0 < num_bytes <= max_len_without_wrapping // no wrapping is necessary
                &&& prev_info.log_plus_pending_length + num_bytes <= log_area_len
                &&& prev_info.head + prev_info.log_plus_pending_length + num_bytes <= u128::MAX
            })
        ensures
            ({
                let prev_info = prev_infos[which_log as int];
                let log_area_len = prev_info.log_area_len;
                let num_bytes = bytes_to_append.len();
                let max_len_without_wrapping = log_area_len -
                    relative_log_pos_to_log_area_offset(prev_info.log_plus_pending_length as int,
                                                        prev_info.head_log_area_offset as int, log_area_len as int);
                // This is how you should update `infos`
                let new_infos = prev_infos.update(which_log as int, LogInfo{
                    log_plus_pending_length: (prev_info.log_plus_pending_length + num_bytes) as u64,
                    ..prev_infos[which_log as int]
                });
                // This is how you should update `state`
                let new_state = prev_state.tentatively_append(which_log as int, bytes_to_append);
                let write_addr = ABSOLUTE_POS_OF_LOG_AREA +
                    relative_log_pos_to_log_area_offset(prev_info.log_plus_pending_length as int,
                                                        prev_info.head_log_area_offset as int,
                                                        log_area_len as int);
                let pm_regions_view2 = pm_regions_view.write(which_log as int, write_addr, bytes_to_append);
                &&& each_metadata_consistent_with_info(pm_regions_view, multilog_id, num_logs, cdb, new_infos)
                // The write doesn't conflict with any outstanding writes
                &&& pm_regions_view.no_outstanding_writes_in_range(which_log as int, write_addr, write_addr + num_bytes)
                &&& memory_matches_deserialized_cdb(pm_regions_view2, cdb)
                &&& each_metadata_consistent_with_info(pm_regions_view2, multilog_id, num_logs, cdb, new_infos)
                &&& each_info_consistent_with_log_area(pm_regions_view2, num_logs, new_infos, new_state)
                &&& new_state.drop_pending_appends() == prev_state.drop_pending_appends()
                // After initiating the write, any crash and recovery will enter the abstract state
                // `new_state.drop_pending_appends()`, so as long as that state is permitted the
                // write will be.
                &&& forall |mem| #[trigger] pm_regions_view2.can_crash_as(mem) ==>
                      recover_all(mem, multilog_id) == Some(new_state.drop_pending_appends())
                // The active metadata is unchanged after the write
                &&& active_metadata_is_equal(pm_regions_view, pm_regions_view2)
                // Metadata types are set after the write and a subsequent commit
                &&& metadata_types_set(pm_regions_view2.committed())
                // Metadata types are set after the write and a subsequent crash
                &&& forall |mem| #[trigger] pm_regions_view2.can_crash_as(mem) ==>
                      metadata_types_set(mem)
                &&& no_outstanding_writes_to_active_metadata(pm_regions_view2, cdb)
            }),
    {
        let w = which_log as int;
        let prev_info = prev_infos[w];
        let log_area_len = prev_info.log_area_len;
        let new_infos = prev_infos.update(which_log as int, LogInfo{
            log_plus_pending_length: (prev_info.log_plus_pending_length + bytes_to_append.len()) as u64,
            ..prev_infos[which_log as int]
        });
        let new_state = prev_state.tentatively_append(which_log as int, bytes_to_append);
        let write_addr = ABSOLUTE_POS_OF_LOG_AREA +
            relative_log_pos_to_log_area_offset(prev_info.log_plus_pending_length as int,
                                                prev_info.head_log_area_offset as int,
                                                log_area_len as int);
        let pm_regions_view2 = pm_regions_view.write(which_log as int, write_addr, bytes_to_append);
        let new_state = prev_state.tentatively_append(w, bytes_to_append);
        let num_bytes = bytes_to_append.len();

        // To prove that the post-write metadata is consistent with
        // `new_infos`, we have to reason about the equivalence of
        // extracted byte sequences that match between the old and new
        // metadata regions.

        assert forall |any_log: u32| #[trigger] log_index_trigger(any_log as int) && any_log < num_logs implies {
            let a = any_log as int;
            metadata_consistent_with_info(pm_regions_view2[a], multilog_id, num_logs, any_log, cdb, new_infos[a])
        } by {
            lemma_metadata_sizes();
            let a = any_log as int;
            lemma_establish_subrange_equivalence(pm_regions_view[a].committed(), pm_regions_view2[a].committed());
        }

        // To prove that the post-write CDB is the same as the
        // pre-write CDB, we have to reason about the equivalence of
        // extracted byte sequences that match between the old and new
        // region #0, where the CDB is stored.

        assert (memory_matches_deserialized_cdb(pm_regions_view2, cdb)) by {
            assert(log_index_trigger(0));
            lemma_establish_subrange_equivalence(pm_regions_view[0].committed(), pm_regions_view2[0].committed());
        }

        // We need extensional equality to reason that the old and new
        // abstract states are the same after dropping pending appends.

        assert(new_state.drop_pending_appends() =~= prev_state.drop_pending_appends());

        // To prove that all crash states after initiating the write
        // are OK, we just have to invoke the following lemma, which
        // requires that our invariants hold.

        lemma_invariants_imply_crash_recover_forall(pm_regions_view2, multilog_id, num_logs, cdb, new_infos, new_state);

        // To prove that there are no outstanding writes in the range
        // where we plan to write, we need to reason about how
        // addresses in the log area correspond to relative log
        // positions. This is because the invariant talks about
        // relative log positions but we're trying to prove something
        // about addresses in the log area (that there are no
        // outstanding writes to certain of them).

        assert(pm_regions_view.no_outstanding_writes_in_range(w, write_addr, write_addr + num_bytes)) by {
            lemma_addresses_in_log_area_correspond_to_relative_log_positions(pm_regions_view[w], prev_info);
        }

        assert(no_outstanding_writes_to_active_metadata(pm_regions_view2, cdb)) by {
            lemma_no_outstanding_writes_to_metadata_implies_no_outstanding_writes_to_active_metadata(
                pm_regions_view2, cdb
            );
        };

        assert(active_metadata_is_equal(pm_regions_view, pm_regions_view2)) by {
            lemma_metadata_sizes();
            assert(pm_regions_view[w].committed().subrange(ABSOLUTE_POS_OF_GLOBAL_METADATA as int,
                                                           ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as int) =~= 
                   pm_regions_view2[w].committed().subrange(ABSOLUTE_POS_OF_GLOBAL_METADATA as int,
                                                            ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as int));
            let log_metadata_pos = get_log_metadata_pos(cdb);
            assert(pm_regions_view[w].committed().subrange(
                log_metadata_pos as int,
                log_metadata_pos + LogMetadata::spec_size_of() + u64::spec_size_of()
            ) == pm_regions_view2[w].committed().subrange(
                log_metadata_pos as int,
                log_metadata_pos + LogMetadata::spec_size_of() + u64::spec_size_of()
            ));
        }

        assert(metadata_types_set(pm_regions_view2.committed())) by {
            lemma_regions_metadata_matches_implies_metadata_types_set(pm_regions_view, pm_regions_view2, cdb);
        }

        assert forall |mem| #[trigger] pm_regions_view2.can_crash_as(mem) implies metadata_types_set(mem) by {
            lemma_metadata_set_after_crash(pm_regions_view2, cdb);
        }
    }

    // This lemma establishes useful facts about performing two
    // contiguous writes, one at the end of the log area and one at
    // the beginning, to effect a tentative append:
    //
    // 1) Each write is permitted because a crash after it's initiated
    // doesn't affect the post-recovery abstract state.
    //
    // 2) The pair of writes maintains invariants, if `infos` and
    // `state` are updated in a certain way.
    //
    // Parameters:
    //
    // `pm_regions_view` -- the view of the persistent memory regions
    // before the write
    //
    // `multilog_id` -- the ID of the multilog stored on that memory
    //
    // `num_logs` -- the number of logs in the multilog
    //
    // `which_log` -- which log among the logs is being tentatively
    // appended to
    //
    // `bytes_to_append` -- what bytes are being tentatively appended
    //
    // `cdb` -- the current corruption-detecting boolean value
    //
    // `prev_infos` -- the pre-append `infos` value
    //
    // `prev_state` -- the pre-append abstract state
    pub proof fn lemma_tentatively_append_wrapping(
        pm_regions_view: PersistentMemoryRegionsView,
        multilog_id: u128,
        num_logs: u32,
        which_log: u32,
        bytes_to_append: Seq<u8>,
        cdb: bool,
        prev_infos: Seq<LogInfo>,
        prev_state: AbstractMultiLogState,
    )
        requires
            log_index_trigger(which_log as int),
            which_log < num_logs,
            memory_matches_deserialized_cdb(pm_regions_view, cdb),
            each_metadata_consistent_with_info(pm_regions_view, multilog_id, num_logs, cdb, prev_infos),
            each_info_consistent_with_log_area(pm_regions_view, num_logs, prev_infos, prev_state),
            no_outstanding_writes_to_metadata(pm_regions_view),
            metadata_types_set(pm_regions_view.committed()),
            forall |i: int| #[trigger] log_index_trigger(i) && 0 <= i < pm_regions_view.len() ==>
                ABSOLUTE_POS_OF_LOG_AREA < pm_regions_view[i].len(),
            ({
                let w = which_log as int;
                let prev_info = prev_infos[w];
                let log_area_len = prev_info.log_area_len;
                let num_bytes = bytes_to_append.len();
                let max_len_without_wrapping = log_area_len -
                    relative_log_pos_to_log_area_offset(prev_info.log_plus_pending_length as int,
                                                        prev_info.head_log_area_offset as int, log_area_len as int);
                &&& num_bytes > max_len_without_wrapping // wrapping is required
                &&& prev_info.head + prev_info.log_plus_pending_length + num_bytes <= u128::MAX
                &&& num_bytes <= log_area_len - prev_info.log_plus_pending_length
            }),
        ensures
            ({
                let w = which_log as int;
                let prev_info = prev_infos[w];
                let log_area_len = prev_info.log_area_len;
                let max_len_without_wrapping = log_area_len -
                    relative_log_pos_to_log_area_offset(prev_info.log_plus_pending_length as int,
                                                        prev_info.head_log_area_offset as int, log_area_len as int);
                let new_infos = prev_infos.update(w, LogInfo{
                    log_plus_pending_length: (prev_info.log_plus_pending_length + bytes_to_append.len()) as u64,
                    ..prev_infos[w]
                });
                let new_state = prev_state.tentatively_append(w, bytes_to_append);
                let bytes_to_append_part1 = bytes_to_append.subrange(0, max_len_without_wrapping as int);
                let bytes_to_append_part2 = bytes_to_append.subrange(max_len_without_wrapping as int,
                                                                     bytes_to_append.len() as int);
                let write_addr = ABSOLUTE_POS_OF_LOG_AREA +
                    relative_log_pos_to_log_area_offset(prev_info.log_plus_pending_length as int,
                                                        prev_info.head_log_area_offset as int,
                                                        log_area_len as int);
                let pm_regions_view2 = pm_regions_view.write(w, write_addr, bytes_to_append_part1);
                let pm_regions_view3 = pm_regions_view2.write(w, ABSOLUTE_POS_OF_LOG_AREA as int, bytes_to_append_part2);
                &&& each_metadata_consistent_with_info(pm_regions_view, multilog_id, num_logs, cdb, new_infos)
                // The first write doesn't conflict with any outstanding writes
                &&& pm_regions_view.no_outstanding_writes_in_range(w, write_addr,
                                                                 write_addr + bytes_to_append_part1.len())
                // The second write also doesn't conflict with any outstanding writes
                &&& pm_regions_view2.no_outstanding_writes_in_range(
                       w,
                       ABSOLUTE_POS_OF_LOG_AREA as int,
                       ABSOLUTE_POS_OF_LOG_AREA + bytes_to_append_part2.len())
                &&& each_metadata_consistent_with_info(pm_regions_view3, multilog_id, num_logs, cdb, new_infos)
                &&& each_info_consistent_with_log_area(pm_regions_view3, num_logs, new_infos, new_state)
                &&& memory_matches_deserialized_cdb(pm_regions_view3, cdb)
                &&& new_state.drop_pending_appends() == prev_state.drop_pending_appends()
                // After initiating the first write, any crash and recovery will enter the abstract
                // state `prev_state.drop_pending_appends()`, so as long as that state is permitted
                // the write will be.
                &&& forall |mem| pm_regions_view2.can_crash_as(mem) ==>
                       recover_all(mem, multilog_id) == Some(prev_state.drop_pending_appends())
                // After initiating the second write, any crash and recovery will enter the abstract
                // state `prev_state.drop_pending_appends()`, so as long as that state is permitted
                // the write will be.
                &&& forall |mem| pm_regions_view3.can_crash_as(mem) ==>
                       recover_all(mem, multilog_id) == Some(prev_state.drop_pending_appends())
                // The active metadata is unchanged after the write
                &&& active_metadata_is_equal(pm_regions_view, pm_regions_view3)
                // Metadata types are set after the write and a subsequent commit
                &&& metadata_types_set(pm_regions_view3.committed())
                // Metadata types are set after each write and a subsequent crash
                &&& forall |mem| #[trigger] pm_regions_view2.can_crash_as(mem) ==>
                      metadata_types_set(mem)
                &&& forall |mem| #[trigger] pm_regions_view3.can_crash_as(mem) ==>
                      metadata_types_set(mem)
                &&& no_outstanding_writes_to_active_metadata(pm_regions_view3, cdb)
            }),
    {
        let w = which_log as int;
        let prev_info = prev_infos[w];
        let log_area_len = prev_info.log_area_len;
        let max_len_without_wrapping = log_area_len -
            relative_log_pos_to_log_area_offset(prev_info.log_plus_pending_length as int,
                                                prev_info.head_log_area_offset as int, log_area_len as int);
        let bytes_to_append_part1 = bytes_to_append.subrange(0, max_len_without_wrapping as int);
        let bytes_to_append_part2 = bytes_to_append.subrange(max_len_without_wrapping as int,
                                                             bytes_to_append.len() as int);
        let intermediate_infos = prev_infos.update(w, LogInfo{
            log_plus_pending_length: (prev_info.log_plus_pending_length + max_len_without_wrapping) as u64,
            ..prev_infos[w]
        });
        let intermediate_state = prev_state.tentatively_append(w, bytes_to_append_part1);
        let new_infos = prev_infos.update(w, LogInfo{
            log_plus_pending_length: (prev_info.log_plus_pending_length + bytes_to_append.len()) as u64,
            ..prev_infos[w]
        });
        let new_state = prev_state.tentatively_append(w, bytes_to_append);
        let write_addr = ABSOLUTE_POS_OF_LOG_AREA +
            relative_log_pos_to_log_area_offset(prev_info.log_plus_pending_length as int,
                                                prev_info.head_log_area_offset as int,
                                                log_area_len as int);
        let pm_regions_view2 = pm_regions_view.write(w, write_addr, bytes_to_append_part1);
        let pm_regions_view3 = pm_regions_view2.write(w, ABSOLUTE_POS_OF_LOG_AREA as int, bytes_to_append_part2);

        // Invoke `lemma_tentatively_append` on each write.

        lemma_tentatively_append(pm_regions_view, multilog_id, num_logs, which_log, bytes_to_append_part1, cdb,
                                 prev_infos, prev_state);
        lemma_tentatively_append(pm_regions_view2, multilog_id, num_logs, which_log, bytes_to_append_part2, cdb,
                                 intermediate_infos, intermediate_state);

        // Use extensional equality to prove the equivalence of the
        // intermediate abstract state between writes and the previous
        // state, if both drop pending appends.

        assert(intermediate_state.drop_pending_appends() =~= prev_state.drop_pending_appends());

        // Use extensional equality to prove the equivalence of the new
        // abstract state, which the caller of this lemma cares about, with
        // an update to the intermediate abstract state, which is what the
        // second call to `lemma_tentatively_append` proves things about.

        assert(new_state =~= intermediate_state.tentatively_append(w, bytes_to_append_part2)) by {
            assert(prev_state[w].pending + bytes_to_append_part1 + bytes_to_append_part2 =~=
                   prev_state[w].pending + bytes_to_append);
        }
    }

}
