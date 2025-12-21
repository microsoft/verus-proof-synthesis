//! This file contains lemmas about tentatively appending to a log.
//!
//! The code in this file is verified and untrusted (as indicated by
//! the `_v.rs` suffix), so you don't have to read it to be confident
//! of the system's correctness.

use crate::log::inv_v::*;
use crate::log::layout_v::*;
use crate::log::logimpl_v::LogInfo;
use crate::log::logspec_t::AbstractLogState;
use crate::pmem::pmemspec_t::PersistentMemoryRegionView;
use crate::pmem::subregion_v::*;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

verus! {
    // This lemma establishes useful facts about performing a
    // contiguous write to effect a tentative append:
    //
    // 1) The write is permitted because, for each address written to,
    //    there's no outstanding write and it's unreachable during
    //    recovery.
    //
    // 2) It maintains invariants, if `info` and `state` are updated
    //    in a certain way.
    //
    // Parameters:
    //
    // `pm_region_view` -- the view of the persistent memory region
    // before the write
    //
    // `log_id` -- the ID of the log stored on that memory
    //
    // `bytes_to_append` -- what bytes are being tentatively appended
    //
    // `cdb` -- the current corruption-detecting boolean value
    //
    // `prev_info` -- the pre-append `info` value
    //
    // `prev_state` -- the pre-append abstract state
    //
    pub proof fn lemma_tentatively_append(
        pm_region_view: PersistentMemoryRegionView,
        bytes_to_append: Seq<u8>,
        prev_info: LogInfo,
        prev_state: AbstractLogState,
    )
        requires
            pm_region_view.len() == prev_info.log_area_len,
            info_consistent_with_log_area(pm_region_view, prev_info, prev_state),
            ({
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
                let log_area_len = prev_info.log_area_len;
                let num_bytes = bytes_to_append.len();
                // This is how you should update `infos`
                let new_info = prev_info.tentatively_append(num_bytes as u64);
                // This is how you should update `state`
                let new_state = prev_state.tentatively_append(bytes_to_append);
                let write_addr =
                    relative_log_pos_to_log_area_offset(prev_info.log_plus_pending_length as int,
                                                        prev_info.head_log_area_offset as int,
                                                        log_area_len as int);
                let pm_region_view2 = pm_region_view.write(write_addr, bytes_to_append);
                &&& pm_region_view.no_outstanding_writes_in_range(write_addr, write_addr + num_bytes)
                &&& forall |log_area_offset: int| write_addr <= log_area_offset < write_addr + num_bytes ==>
                       log_area_offset_unreachable_during_recovery(prev_info.head_log_area_offset as int,
                                                                   prev_info.log_area_len as int,
                                                                   prev_info.log_length as int,
                                                                   log_area_offset)
                &&& info_consistent_with_log_area(pm_region_view2, new_info, new_state)
            }),
    {
        let new_state = prev_state.tentatively_append(bytes_to_append);

        // We need extensional equality to reason that the old and new
        // abstract states are the same after dropping pending appends.

        assert(new_state.drop_pending_appends() =~= prev_state.drop_pending_appends());

        // To prove that there are no outstanding writes in the range
        // where we plan to write, we need to reason about how
        // addresses in the log area correspond to relative log
        // positions. This is because the invariant talks about
        // relative log positions but we're trying to prove something
        // about addresses in the log area (that there are no
        // outstanding writes to certain of them).

        lemma_addresses_in_log_area_subregion_correspond_to_relative_log_positions(pm_region_view, prev_info);
    }

    // This lemma establishes useful facts about performing two
    // contiguous writes, one at the end of the log area and one at
    // the beginning, to effect a tentative append:
    //
    // 1) Each write is permitted because there are no outstanding writes
    //    to the range of addresses to write to.
    //
    // 2) The pair of writes maintains invariants, if `infos` and
    //    `state` are updated in a certain way.
    //
    // Parameters:
    //
    // `pm_region_view` -- the view of the persistent memory regions
    // before the write
    //
    // `log_id` -- the ID of the log stored on that memory
    //
    // `bytes_to_append` -- what bytes are being tentatively appended
    //
    // `cdb` -- the current corruption-detecting boolean value
    //
    // `prev_info` -- the pre-append `info` value
    //
    // `prev_state` -- the pre-append abstract state
   pub proof fn lemma_tentatively_append_wrapping(
        pm_region_view: PersistentMemoryRegionView,
        bytes_to_append: Seq<u8>,
        prev_info: LogInfo,
        prev_state: AbstractLogState,
    )
        requires
            pm_region_view.len() == prev_info.log_area_len,
            info_consistent_with_log_area(pm_region_view, prev_info, prev_state),
            ({
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
                let log_area_len = prev_info.log_area_len;
                let max_len_without_wrapping = log_area_len -
                    relative_log_pos_to_log_area_offset(prev_info.log_plus_pending_length as int,
                                                        prev_info.head_log_area_offset as int, log_area_len as int);
                let new_info = prev_info.tentatively_append(bytes_to_append.len() as u64);
                let new_state = prev_state.tentatively_append(bytes_to_append);
                let bytes_to_append_part1 = bytes_to_append.subrange(0, max_len_without_wrapping as int);
                let bytes_to_append_part2 = bytes_to_append.subrange(max_len_without_wrapping as int,
                                                                     bytes_to_append.len() as int);
                let write_addr =
                    relative_log_pos_to_log_area_offset(prev_info.log_plus_pending_length as int,
                                                        prev_info.head_log_area_offset as int,
                                                        log_area_len as int);
                let pm_region_view2 = pm_region_view.write(write_addr, bytes_to_append_part1);
                let pm_region_view3 = pm_region_view2.write(0int, bytes_to_append_part2);
                // The first write doesn't conflict with any outstanding writes
                &&& pm_region_view.no_outstanding_writes_in_range(write_addr,
                                                                 write_addr + bytes_to_append_part1.len())
                // The first write is only to log area offsets unreachable during recovery
                &&& forall |log_area_offset: int| write_addr <= log_area_offset < write_addr + bytes_to_append_part1.len() ==>
                       log_area_offset_unreachable_during_recovery(prev_info.head_log_area_offset as int,
                                                                   prev_info.log_area_len as int,
                                                                   prev_info.log_length as int,
                                                                   log_area_offset)
                // The second write also doesn't conflict with any outstanding writes
                &&& pm_region_view2.no_outstanding_writes_in_range(0int, bytes_to_append_part2.len() as int)
                // The second write is also only to log area offsets unreachable during recovery
                &&& forall |log_area_offset: int| 0 <= log_area_offset < bytes_to_append_part2.len() ==>
                       log_area_offset_unreachable_during_recovery(prev_info.head_log_area_offset as int,
                                                                   prev_info.log_area_len as int,
                                                                   prev_info.log_length as int,
                                                                   log_area_offset)
                // After the writes, the log area will be consistent with an updated info and state.
                &&& info_consistent_with_log_area(pm_region_view3, new_info, new_state)
            }),
    {
        let log_area_len = prev_info.log_area_len;
        let max_len_without_wrapping = log_area_len -
            relative_log_pos_to_log_area_offset(prev_info.log_plus_pending_length as int,
                                                prev_info.head_log_area_offset as int, log_area_len as int);
        let bytes_to_append_part1 = bytes_to_append.subrange(0, max_len_without_wrapping as int);
        let bytes_to_append_part2 = bytes_to_append.subrange(max_len_without_wrapping as int,
                                                             bytes_to_append.len() as int);
        let intermediate_info = LogInfo{
            log_plus_pending_length: (prev_info.log_plus_pending_length + max_len_without_wrapping) as u64,
            ..prev_info
        };
        let intermediate_state = prev_state.tentatively_append(bytes_to_append_part1);
        let new_state = prev_state.tentatively_append(bytes_to_append);
        let write_addr =
            relative_log_pos_to_log_area_offset(prev_info.log_plus_pending_length as int,
                                                prev_info.head_log_area_offset as int,
                                                log_area_len as int);
        let pm_region_view2 = pm_region_view.write(write_addr, bytes_to_append_part1);

        // Invoke `lemma_tentatively_append` on each write.

        lemma_tentatively_append(pm_region_view, bytes_to_append_part1, prev_info, prev_state);
        lemma_tentatively_append(pm_region_view2, bytes_to_append_part2, intermediate_info, intermediate_state);
    }

}
