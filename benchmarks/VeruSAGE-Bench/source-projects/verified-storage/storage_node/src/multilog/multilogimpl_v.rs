//! This file contains the implementation of `UntrustedMultiLogImpl`,
//! which implements a provably correct multilog.
//!
//! The code in this file is verified and untrusted (as indicated by
//! the `_v.rs` suffix), so you don't have to read it to be confident
//! of the system's correctness.

use crate::log::inv_v::lemma_auto_smaller_range_of_seq_is_subrange;
use crate::log::inv_v::lemma_metadata_matches_implies_metadata_types_set;
use crate::multilog::append_v::*;
use crate::multilog::inv_v::*;
use crate::multilog::layout_v::*;
use crate::multilog::multilogimpl_t::*;
use crate::multilog::multilogspec_t::AbstractMultiLogState;
use crate::multilog::setup_v::{
    check_for_required_space, compute_log_capacities, write_setup_metadata_to_all_regions,
};
use crate::multilog::start_v::{read_cdb, read_logs_variables};
use crate::pmem::crc_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::wrpm_t::*;
use crate::pmem::traits_t::size_of;
use builtin::*;
use builtin_macros::*;
use vstd::arithmetic::div_mod::*;
use vstd::bytes::*;
use vstd::prelude::*;
use vstd::slice::*;

verus! {

    // This structure, `LogInfo`, is used by `UntrustedMultiLogImpl`
    // to store information about a single log. Its fields are:
    //
    // `log_area_len` -- how many bytes are in the log area on
    //     persistent memory
    //
    // `head` -- the logical position of the log's head
    //
    // `head_log_area_offset` -- the offset into the log area
    //     holding the byte at the head position. This is
    //     always equal to `head % log_area_len`, and is
    //     cached in this variable to avoid expensive modulo
    //     operations.
    //
    // `log_length` -- the number of bytes in the log beyond the head
    //
    // `log_plus_pending_length` -- the number of bytes in the log and
    //     the pending appends to the log combined
    pub struct LogInfo {
        pub log_area_len: u64,
        pub head: u128,
        pub head_log_area_offset: u64,
        pub log_length: u64,
        pub log_plus_pending_length: u64,
    }

    // This structure, `UntrustedMultiLogImpl`, implements a
    // multilog. Its fields are:
    //
    // `num_logs` -- the number of logs in the multilog
    // `cdb` -- the current value of the corruption-detecting boolean
    // `infos` -- a vector of `LogInfo`s, one per log
    // `state` -- the abstract view of the multilog
    pub struct UntrustedMultiLogImpl {
        num_logs: u32,
        cdb: bool,
        infos: Vec<LogInfo>,
        state: Ghost<AbstractMultiLogState>
    }

    impl UntrustedMultiLogImpl
    {
        // This static function specifies how multiple regions'
        // contents should be viewed upon recovery as an abstract
        // multilog state.
        pub closed spec fn recover(mems: Seq<Seq<u8>>, multilog_id: u128) -> Option<AbstractMultiLogState>
        {
            if !metadata_types_set(mems) {
                // If the metadata types aren't properly set up, the log is unrecoverable.
                None
            } else {
                recover_all(mems, multilog_id)
            }
        }

        // This method specifies an invariant on `self` that all
        // `UntrustedMultiLogImpl` methods maintain. It requires this
        // invariant to hold on any method invocation, and ensures it
        // in any method invocation that takes `&mut self`.
        //
        // Most of the conjuncts in this invariant are defined in the
        // file `inv_v.rs`. See that file for detailed explanations.
        pub closed spec fn inv<Perm, PMRegions>(
            &self,
            wrpm_regions: &WriteRestrictedPersistentMemoryRegions<Perm, PMRegions>,
            multilog_id: u128,
        ) -> bool
            where
                Perm: CheckPermission<Seq<Seq<u8>>>,
                PMRegions: PersistentMemoryRegions
        {
            &&& wrpm_regions.inv() // whatever the persistent memory regions require as an invariant
            &&& no_outstanding_writes_to_metadata(wrpm_regions@)
            &&& memory_matches_deserialized_cdb(wrpm_regions@, self.cdb)
            &&& each_metadata_consistent_with_info(wrpm_regions@, multilog_id, self.num_logs, self.cdb, self.infos@)
            &&& each_info_consistent_with_log_area(wrpm_regions@, self.num_logs, self.infos@, self.state@)
            &&& can_only_crash_as_state(wrpm_regions@, multilog_id, self.state@.drop_pending_appends())
            &&& metadata_types_set(wrpm_regions@.committed())
            &&& forall |i: int| #[trigger] log_index_trigger(i) && 0 <= i < wrpm_regions@.len() ==>
                   ABSOLUTE_POS_OF_LOG_AREA < wrpm_regions@[i].len()
        }

        pub proof fn lemma_inv_implies_wrpm_inv<Perm, PMRegions>(
            &self,
            wrpm_regions: &WriteRestrictedPersistentMemoryRegions<Perm, PMRegions>,
            multilog_id: u128
        )
            where
                Perm: CheckPermission<Seq<Seq<u8>>>,
                PMRegions: PersistentMemoryRegions
            requires
                self.inv(wrpm_regions, multilog_id)
            ensures
                wrpm_regions.inv()
        {}

        pub proof fn lemma_inv_implies_can_only_crash_as<Perm, PMRegions>(
            &self,
            wrpm_regions: &WriteRestrictedPersistentMemoryRegions<Perm, PMRegions>,
            multilog_id: u128
        )
            where
                Perm: CheckPermission<Seq<Seq<u8>>>,
                PMRegions: PersistentMemoryRegions
            requires
                self.inv(wrpm_regions, multilog_id)
            ensures
                can_only_crash_as_state(wrpm_regions@, multilog_id, self@.drop_pending_appends())
        {}

        // This function specifies how to view the in-memory state of
        // `self` as an abstract multilog state.
        pub closed spec fn view(&self) -> AbstractMultiLogState
        {
            self.state@
        }

        // The `setup` method sets up persistent memory objects `pm_regions`
        // to store an initial empty multilog. It returns a vector
        // listing the capacities of the logs. See `README.md` for more
        // documentation.
        pub exec fn setup<PMRegions>(
            pm_regions: &mut PMRegions,
            multilog_id: u128,
        ) -> (result: Result<Vec<u64>, MultiLogErr>)
            where
                PMRegions: PersistentMemoryRegions
            requires
                old(pm_regions).inv(),
            ensures
                pm_regions.inv(),
                pm_regions.constants() == old(pm_regions).constants(),
                pm_regions@.no_outstanding_writes(),
                match result {
                    Ok(log_capacities) => {
                        let state = AbstractMultiLogState::initialize(log_capacities@);
                        &&& pm_regions@.len() == old(pm_regions)@.len()
                        &&& pm_regions@.len() >= 1
                        &&& pm_regions@.len() <= u32::MAX
                        &&& log_capacities@.len() == pm_regions@.len()
                        &&& forall |i: int| 0 <= i < pm_regions@.len() ==> #[trigger] log_capacities@[i] <= pm_regions@[i].len()
                        &&& forall |i: int| 0 <= i < pm_regions@.len() ==>
                               #[trigger] pm_regions@[i].len() == old(pm_regions)@[i].len()
                        &&& can_only_crash_as_state(pm_regions@, multilog_id, state)
                        &&& Self::recover(pm_regions@.committed(), multilog_id) == Some(state)
                        &&& Self::recover(pm_regions@.flush().committed(), multilog_id) == Some(state)
                        &&& state == state.drop_pending_appends()
                    },
                    Err(MultiLogErr::InsufficientSpaceForSetup { which_log, required_space }) => {
                        let flushed_regions = old(pm_regions)@.flush();
                        &&& pm_regions@ == flushed_regions
                        &&& pm_regions@[which_log as int].len() < required_space
                    },
                    Err(MultiLogErr::CantSetupWithFewerThanOneRegion { }) => {
                        let flushed_regions = old(pm_regions)@.flush();
                        &&& pm_regions@ == flushed_regions
                        &&& pm_regions@.len() < 1
                    },
                    Err(MultiLogErr::CantSetupWithMoreThanU32MaxRegions { }) => {
                        let flushed_regions = old(pm_regions)@.flush();
                        &&& pm_regions@ == flushed_regions
                        &&& pm_regions@.len() > u32::MAX
                    },
                    _ => false
                }
        {
            let ghost original_pm_regions = pm_regions@;

            // We can't write without proving that there are no
            // outstanding writes where we're writing. So just start
            // out by flushing, so it's clear we can write anywhere.
            //
            // Why can't we write without proving there isn't a
            // conflicting outstanding write, you ask? Two reasons:
            //
            // First, to simplify the specification of how persistent
            // memory behaves, in `pmem::pmemspec_t.rs` we don't specify
            // what happens when there are multiple outstanding writes
            // to the same address. Instead, we just forbid that
            // case.
            //
            // Second, even if we did specify what happened in that
            // case, in this function we have no idea what's already
            // been written. If there were outstanding writes and they
            // got reordered after our writes, the resulting state
            // might be invalid. So we need to flush before writing
            // anything anyway.

            pm_regions.flush();

            // Get the list of region sizes and make sure they support
            // storing a multilog. If not, return an appropriate
            // error.

            let region_sizes = get_region_sizes(pm_regions);
            let num_regions = region_sizes.len();

            if num_regions < 1 {
                return Err(MultiLogErr::CantSetupWithFewerThanOneRegion { });
            }
            if num_regions > u32::MAX as usize {
                return Err(MultiLogErr::CantSetupWithMoreThanU32MaxRegions { });
            }
            let num_logs = num_regions as u32;
            check_for_required_space(&region_sizes, num_logs)?;

            // Compute log capacities so we can return them.

            let log_capacities = compute_log_capacities(&region_sizes);

            // Write setup metadata to all regions.

            write_setup_metadata_to_all_regions(pm_regions, &region_sizes, Ghost(log_capacities@), multilog_id);

            proof {
                // Prove various postconditions about how we can
                // crash. Specifically, (1) we can only crash as
                // `AbstractMultiLogState::initialize(log_capacities@)`,
                // (2) if we recover after flushing then we get that
                // state, and (3) that state has no pending appends.

                let state = AbstractMultiLogState::initialize(log_capacities@);
                assert(state =~= state.drop_pending_appends());
                lemma_if_no_outstanding_writes_then_flush_is_idempotent(pm_regions@);
                lemma_if_no_outstanding_writes_then_persistent_memory_regions_view_can_only_crash_as_committed(
                    pm_regions@);

                // Convert quantifiers triggered on
                // `log_index_trigger` to ones that use triggers in
                // the postcondition specified for this function.

                assert(forall |i: int| log_index_trigger(i) && 0 <= i < pm_regions@.len() ==>
                       #[trigger] log_capacities@[i] <= pm_regions@[i].len());
                assert(forall |i: int| log_index_trigger(i) && 0 <= i < pm_regions@.len() ==>
                       #[trigger] pm_regions@[i].len() == old(pm_regions)@[i].len());
                
            }

            Ok(log_capacities)
        }

        // The `start` static method creates an
        // `UntrustedMultiLogImpl` out of a set of persistent memory
        // regions. It's assumed that those regions were initialized
        // with `setup` and then only `UntrustedMultiLogImpl` methods
        // were allowed to mutate them. See `README.md` for more
        // documentation and an example of its use.
        //
        // This method is passed a write-restricted collection of
        // persistent memory regions `wrpm_regions`. This restricts
        // how we can write `wrpm_regions`. This is moot, though,
        // because we don't ever write to the memory.
        pub exec fn start<PMRegions>(
            wrpm_regions: &mut WriteRestrictedPersistentMemoryRegions<TrustedMultiLogPermission, PMRegions>,
            multilog_id: u128,
            Tracked(perm): Tracked<&TrustedMultiLogPermission>,
            Ghost(state): Ghost<AbstractMultiLogState>,
        ) -> (result: Result<Self, MultiLogErr>)
            where
                PMRegions: PersistentMemoryRegions
            requires
                Self::recover(old(wrpm_regions)@.flush().committed(), multilog_id) == Some(state),
                old(wrpm_regions).inv(),
                forall |s| #[trigger] perm.check_permission(s) <==> Self::recover(s, multilog_id) == Some(state),
            ensures
                wrpm_regions.inv(),
                wrpm_regions.constants() == old(wrpm_regions).constants(),
                match result {
                    Ok(log_impl) => {
                        &&& log_impl.inv(wrpm_regions, multilog_id)
                        &&& log_impl@ == state
                        &&& can_only_crash_as_state(wrpm_regions@, multilog_id, state.drop_pending_appends())
                    },
                    Err(MultiLogErr::CRCMismatch) => !wrpm_regions.constants().impervious_to_corruption,
                    Err(MultiLogErr::InsufficientSpaceForSetup { which_log, required_space }) => {
                        let flushed_regions = old(wrpm_regions)@.flush();
                        &&& 0 <= which_log < flushed_regions.len()
                        &&& wrpm_regions@ == flushed_regions
                        &&& wrpm_regions@[which_log as int].len() < required_space
                    },
                    _ => false
                }
        {
            // The invariants demand that there are no outstanding
            // writes to various location. To make sure of this, we
            // flush all memory regions.

            wrpm_regions.flush();

            // Out of paranoia, we check to make sure that the number
            // of regions is sensible. Both cases are technically
            // precluded by the assumptions about how `start` is
            // invoked, since it's assumed the user invokes `start` on
            // a properly set-up collection of persistent memory
            // regions. We check for them anyway in case that
            // assumption doesn't hold.

            let pm_regions = wrpm_regions.get_pm_regions_ref();
            let num_regions = pm_regions.get_num_regions();
            let region_sizes = get_region_sizes(pm_regions);
            if num_regions < 1 {
                assert(false);
                return Err(MultiLogErr::CantSetupWithFewerThanOneRegion { });
            }
            if num_regions > u32::MAX as usize {
                assert(false);
                return Err(MultiLogErr::CantSetupWithMoreThanU32MaxRegions { });
            }
            let num_logs = num_regions as u32;
            check_for_required_space(&region_sizes, num_logs)?;

            // First, we read the corruption-detecting boolean and
            // return an error if that fails.

            let cdb = read_cdb(pm_regions)?;

            // Second, we read the logs variables to store in
            // `infos`. If that fails, we return an error.

            let infos = read_logs_variables(pm_regions, multilog_id, cdb, num_logs, Ghost(state))?;
            proof {
                // We have to prove that we can only crash as the given abstract
                // state with all pending appends dropped. We prove this with two
                // lemmas. The first says that since we've established certain
                // invariants, we can only crash as `state`. The second says that,
                // because this is a recovered state, it's unaffected by dropping
                // all pending appends.

                lemma_invariants_imply_crash_recover_forall(pm_regions@, multilog_id, num_logs, cdb,
                                                            infos@, state);
                lemma_recovered_state_is_crash_idempotent(wrpm_regions@.committed(), multilog_id);
                assert(no_outstanding_writes_to_metadata(wrpm_regions@));
                lemma_no_outstanding_writes_to_metadata_implies_no_outstanding_writes_to_active_metadata(wrpm_regions@,
                                                                                                         cdb);

                lemma_metadata_set_after_crash(wrpm_regions@, cdb);
            }
            Ok(Self{ num_logs, cdb, infos, state: Ghost(state) })
        }

        // The `tentatively_append` method tentatively appends
        // `bytes_to_append` to the end of log number `which_log` in
        // the multilog. It's tentative in that crashes will undo the
        // appends, and reads aren't allowed in the tentative part of
        // the log. See `README.md` for more documentation and examples
        // of its use.
        //
        // This method is passed a write-restricted collection of
        // persistent memory regions `wrpm_regions`. This restricts
        // how it can write `wrpm_regions`. It's only given permission
        // (in `perm`) to write if it can prove that any crash after
        // initiating the write is safe. That is, any such crash must
        // put the memory in a state that recovers as the current
        // abstract state with all pending appends dropped.
        pub exec fn tentatively_append<PMRegions>(
            &mut self,
            wrpm_regions: &mut WriteRestrictedPersistentMemoryRegions<TrustedMultiLogPermission, PMRegions>,
            which_log: u32,
            bytes_to_append: &[u8],
            Ghost(multilog_id): Ghost<u128>,
            Tracked(perm): Tracked<&TrustedMultiLogPermission>,
        ) -> (result: Result<u128, MultiLogErr>)
            where
                PMRegions: PersistentMemoryRegions
            requires
                old(self).inv(&*old(wrpm_regions), multilog_id),
                forall |s| #[trigger] perm.check_permission(s) <==>
                    Self::recover(s, multilog_id) == Some(old(self)@.drop_pending_appends()),
            ensures
                self.inv(wrpm_regions, multilog_id),
                wrpm_regions.constants() == old(wrpm_regions).constants(),
                can_only_crash_as_state(wrpm_regions@, multilog_id, self@.drop_pending_appends()),
                match result {
                    Ok(offset) => {
                        let state = old(self)@[which_log as int];
                        &&& which_log < old(self)@.num_logs()
                        &&& offset == state.head + state.log.len() + state.pending.len()
                        &&& self@ == old(self)@.tentatively_append(which_log as int, bytes_to_append@)
                    },
                    Err(MultiLogErr::InvalidLogIndex { }) => {
                        &&& self@ == old(self)@
                        &&& which_log >= self@.num_logs()
                    },
                    Err(MultiLogErr::InsufficientSpaceForAppend { available_space }) => {
                        &&& self@ == old(self)@
                        &&& which_log < self@.num_logs()
                        &&& available_space < bytes_to_append@.len()
                        &&& {
                               let state = self@[which_log as int];
                               ||| available_space == state.capacity - state.log.len() - state.pending.len()
                               ||| available_space == u128::MAX - state.head - state.log.len() - state.pending.len()
                           }
                    },
                    _ => false
                }
        {
            // If an invalid log index was requested, return an error.

            if which_log >= self.num_logs {
                return Err(MultiLogErr::InvalidLogIndex{ });
            }

            // Mention `log_index_trigger` for `which_log` to trigger
            // various useful `forall`s in invariants and thereby make
            // the verifier aware of important per-log invariants
            // about log number `which_log`.

            assert(log_index_trigger(which_log as int));

            let info = &self.infos[which_log as usize];

            // For instance, one useful invariant we triggered above
            // implies that `info.log_plus_pending_length <=
            // info.log_area_len`, so we know we can safely do the
            // following subtraction without underflow.

            let available_space: u64 = info.log_area_len - info.log_plus_pending_length as u64;

            // Check to make sure we have enough available space, and
            // return an error otherwise. There are two ways we might
            // not have available space. The first is that doing the
            // append would overfill the log area. The second (which
            // will probably never happen) is that doing this append
            // and a subsequent commit would make the logical tail
            // exceed u128::MAX.

            let num_bytes: u64 = bytes_to_append.len() as u64;
            if num_bytes > available_space {
                return Err(MultiLogErr::InsufficientSpaceForAppend{ available_space })
            }
            if num_bytes as u128 > u128::MAX - info.log_plus_pending_length as u128 - info.head {
                return Err(MultiLogErr::InsufficientSpaceForAppend{
                    available_space: (u128::MAX - info.log_plus_pending_length as u128 - info.head) as u64
                })
            }

            // Compute the current logical offset of the end of the
            // log, including any earlier pending appends. This is the
            // offset at which we'll be logically appending, and so is
            // the offset we're expected to return. After all, the
            // caller wants to know what virtual log position they
            // need to use to read this data in the future.

            let old_pending_tail: u128 = info.head + info.log_plus_pending_length as u128;

            let ghost w = which_log as int;
            let ghost state = self.state@[w];

            // The simple case is that we're being asked to append the
            // empty string. If so, do nothing and return.

            if num_bytes == 0 {
                assert(forall |a: Seq<u8>, b: Seq<u8>| b == Seq::<u8>::empty() ==> a + b == a);
                assert(bytes_to_append@ =~= Seq::<u8>::empty());
                assert(self@ =~= old(self)@.tentatively_append(w, bytes_to_append@));
                return Ok(old_pending_tail);
            }

            // If the number of bytes in the log plus pending appends
            // is at least as many bytes as are beyond the head in the
            // log area, there's obviously enough room to append all
            // the bytes without wrapping. So just write the bytes
            // there.

            if info.log_plus_pending_length >= info.log_area_len - info.head_log_area_offset {

                // We could compute the address to write to with:
                //
                // `write_addr = ABSOLUTE_POS_OF_LOG_AREA + old_pending_tail % info.log_area_len;`
                //
                // But we can replace the expensive modulo operation above with two subtraction
                // operations as follows. This is somewhat subtle, but we have verification backing
                // us up and proving this optimization correct.

                let write_addr: u64 = ABSOLUTE_POS_OF_LOG_AREA +
                    info.log_plus_pending_length - (info.log_area_len - info.head_log_area_offset);
                assert(write_addr == ABSOLUTE_POS_OF_LOG_AREA +
                       relative_log_pos_to_log_area_offset(info.log_plus_pending_length as int,
                                                           info.head_log_area_offset as int,
                                                           info.log_area_len as int));

                proof {
                    lemma_tentatively_append(wrpm_regions@, multilog_id, self.num_logs, which_log,
                                             bytes_to_append@, self.cdb, self.infos@, self.state@);
                }
                    
                wrpm_regions.write(which_log as usize, write_addr, bytes_to_append, Tracked(perm));
            }
            else {
                // We could compute the address to write to with:
                //
                // `write_addr = ABSOLUTE_POS_OF_LOG_AREA + old_pending_tail % info.log_area_len`
                //
                // But we can replace the expensive modulo operation above with an addition
                // operation as follows. This is somewhat subtle, but we have verification backing
                // us up and proving this optimization correct.

                let write_addr: u64 = ABSOLUTE_POS_OF_LOG_AREA +
                    info.log_plus_pending_length + info.head_log_area_offset;
                assert(write_addr == ABSOLUTE_POS_OF_LOG_AREA +
                       relative_log_pos_to_log_area_offset(info.log_plus_pending_length as int,
                                                           info.head_log_area_offset as int,
                                                           info.log_area_len as int));

                // There's limited space beyond the pending bytes in the log area, so as we write
                // the bytes we may have to wrap around the end of the log area. So we must compute
                // how many bytes we can write without having to wrap:

                let max_len_without_wrapping: u64 =
                    info.log_area_len - info.head_log_area_offset - info.log_plus_pending_length;
                assert(max_len_without_wrapping == info.log_area_len -
                       relative_log_pos_to_log_area_offset(info.log_plus_pending_length as int,
                                                           info.head_log_area_offset as int, info.log_area_len as int));

                if num_bytes <= max_len_without_wrapping {

                    // If there's room for all the bytes we need to write, we just need one write.

                    proof {
                        lemma_tentatively_append(wrpm_regions@, multilog_id, self.num_logs, which_log,
                                                 bytes_to_append@, self.cdb, self.infos@, self.state@);
                    }
                    wrpm_regions.write(which_log as usize, write_addr, bytes_to_append, Tracked(perm));
                }
                else {

                    // If there isn't room for all the bytes we need to write, we need two writes,
                    // one writing the first `max_len_without_wrapping` bytes to address
                    // `write_addr` and the other writing the remaining bytes to the beginning of
                    // the log area (`ABSOLUTE_POS_OF_LOG_AREA`).
                    //
                    // There are a lot of things we have to prove about these writes, like the fact
                    // that they're both permitted by `perm`. We offload those proofs to a lemma in
                    // `append_v.rs` that we invoke here.

                    proof {
                        lemma_tentatively_append_wrapping(wrpm_regions@, multilog_id, self.num_logs, which_log,
                                                          bytes_to_append@, self.cdb, self.infos@, self.state@);
                    }
                    wrpm_regions.write(which_log as usize, write_addr,
                                       slice_subrange(bytes_to_append, 0, max_len_without_wrapping as usize),
                                       Tracked(perm));
                    wrpm_regions.write(which_log as usize, ABSOLUTE_POS_OF_LOG_AREA,
                                       slice_subrange(bytes_to_append, max_len_without_wrapping as usize,
                                                      bytes_to_append.len()),
                                       Tracked(perm));
                }
            }

            // We now update our `infos` field to reflect the new
            // `log_plus_pending_length` value.

            let new_info = LogInfo{
                log_plus_pending_length: (info.log_plus_pending_length + num_bytes) as u64,
                ..self.infos[which_log as usize]
            };
            self.infos.set(which_log as usize, new_info);

            // We update our `state` field to reflect the tentative append.

            self.state = Ghost(self.state@.tentatively_append(which_log as int, bytes_to_append@));

            Ok(old_pending_tail)
        }

        // This local helper method updates the log metadata on
        // persistent memory to be consistent with `self.infos` and
        // `self.state`. It does so in the following steps: (1) update, in
        // each region, the log metadata corresponding to the inactive
        // CDB; (2) flush; (3) swap the CDB in region #0; (4) flush again.
        //
        // The first of these steps only writes to inactive metadata, i.e.,
        // metadata that's ignored during recovery. So even if a crash
        // happens during or immediately after this call, recovery will be
        // unaffected.
        //
        // Before calling this function, the caller should make sure that
        // `self.infos` and `self.state` contain the data that the inactive
        // log metadata should reflect. But, since this function has to
        // reason about crashes, it also needs to know things about the
        // *previous* values of `self.infos` and `self.state`, since those
        // are the ones that the active log metadata is consistent with
        // and will stay consistent with until we write the new CDB. These
        // previous values are passed as ghost parameters since they're
        // only needed for proving things.
        //
        // The caller of this function is responsible for making sure that
        // the contents of the log area are compatible with both the old
        // and the new `infos` and `state`. However, the log area contents
        // only need to be compatible with the new `infos` and `state`
        // after the next flush, since we're going to be doing a flush.
        // This weaker requirement allows a performance optimization: the
        // caller doesn't have to flush before calling this function.
        exec fn update_log_metadata<PMRegions>(
            &mut self,
            wrpm_regions: &mut WriteRestrictedPersistentMemoryRegions<TrustedMultiLogPermission, PMRegions>,
            Ghost(multilog_id): Ghost<u128>,
            Ghost(prev_infos): Ghost<Seq<LogInfo>>,
            Ghost(prev_state): Ghost<AbstractMultiLogState>,
            Tracked(perm): Tracked<&TrustedMultiLogPermission>,
        )
            where
                PMRegions: PersistentMemoryRegions
            requires
                old(wrpm_regions).inv(),
                memory_matches_deserialized_cdb(old(wrpm_regions)@, old(self).cdb),
                no_outstanding_writes_to_metadata(old(wrpm_regions)@),
                each_metadata_consistent_with_info(old(wrpm_regions)@, multilog_id, old(self).num_logs,
                                                   old(self).cdb, prev_infos),
                each_info_consistent_with_log_area(old(wrpm_regions)@.flush(), old(self).num_logs,
                                                old(self).infos@, old(self).state@),
                each_info_consistent_with_log_area(old(wrpm_regions)@, old(self).num_logs, prev_infos, prev_state),
                forall |which_log: int| #[trigger] log_index_trigger(which_log) && 0 <= which_log < old(self).num_logs ==>
                    old(self).infos@[which_log].log_area_len == prev_infos[which_log].log_area_len,
                forall |s| {
                          ||| Self::recover(s, multilog_id) == Some(prev_state.drop_pending_appends())
                          ||| Self::recover(s, multilog_id) == Some(old(self).state@.drop_pending_appends())
                      } ==> #[trigger] perm.check_permission(s),
                metadata_types_set(old(wrpm_regions)@.committed()),
                forall |i: int| #[trigger] log_index_trigger(i) && 0 <= i < old(wrpm_regions)@.len() ==>
                    ABSOLUTE_POS_OF_LOG_AREA < old(wrpm_regions)@[i].len(),
                old(wrpm_regions)@.len() > 0,
            ensures
                self.inv(wrpm_regions, multilog_id),
                wrpm_regions.constants() == old(wrpm_regions).constants(),
                self.state == old(self).state,
        {
            broadcast use pmcopy_axioms;
                
            // Set the `unused_metadata_pos` to be the position corresponding to !self.cdb
            // since we're writing in the inactive part of the metadata.

            let unused_metadata_pos = if self.cdb { ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE }
                                      else { ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_TRUE };
            assert(unused_metadata_pos == get_log_metadata_pos(!self.cdb));
            assert(log_index_trigger(0));

            // Loop, each time performing the update of the inactive log
            // metadata for log number `current_log`.

            let ghost old_wrpm_regions = wrpm_regions@;
            proof {
                // Before we enter the loop, we need to prove that there are no outstanding writes to active
                // metadata to satisfy the invariant. This follows from the fact that there are no outstanding 
                // writes to *any* metadata, but Z3 needs a hint from the lemma.
                lemma_no_outstanding_writes_to_metadata_implies_no_outstanding_writes_to_active_metadata(
                    wrpm_regions@, self.cdb);
            }

            self.update_inactive_log_metadata(wrpm_regions, Ghost(multilog_id), Ghost(prev_infos), Ghost(prev_state), Tracked(perm));

            assert(self.num_logs == wrpm_regions@.len());
            assert(forall |i: int| #[trigger] log_index_trigger(i) && 0 <= i < wrpm_regions@.len() ==>
                    inactive_metadata_types_set_in_region(wrpm_regions@.flush().committed()[i], self.cdb));

            proof {
                // Prove that after the flush we're about to do, all our
                // invariants will continue to hold (using the still-unchanged
                // CDB and the old metadata, infos, and state).
                lemma_flushing_metadata_maintains_invariants(wrpm_regions@, multilog_id, self.num_logs, self.cdb,
                                                             prev_infos, prev_state);

                // Also, prove that metadata types will still be set after the flush.
                lemma_no_outstanding_writes_to_active_metadata_implies_metadata_types_set_after_flush(wrpm_regions@,
                                                                                                      self.cdb);
            }

            // Next, flush all outstanding writes to memory. This is
            // necessary so that those writes are ordered before the update
            // to the CDB.
            wrpm_regions.flush();

            // Next, compute the new encoded CDB to write.

            let new_cdb = if self.cdb { CDB_FALSE } else { CDB_TRUE };
            let ghost new_cdb_bytes = new_cdb.spec_to_bytes();

            // Show that after writing and flushing, the CDB will be !self.cdb

            let ghost pm_regions_after_write = wrpm_regions@.write(0int, ABSOLUTE_POS_OF_LOG_CDB as int, new_cdb_bytes);
            let ghost flushed_mem_after_write = pm_regions_after_write.flush();
            assert(memory_matches_deserialized_cdb(flushed_mem_after_write, !self.cdb)) by {
                let flushed_regions = pm_regions_after_write.flush();
                lemma_write_reflected_after_flush_committed(wrpm_regions@[0], ABSOLUTE_POS_OF_LOG_CDB as int,
                                                            new_cdb_bytes);
                assert(deserialize_log_cdb(flushed_regions[0].committed()) == new_cdb);
            }

            // Show that after writing and flushing, our invariants will
            // hold for each log if we flip `self.cdb`.

            let ghost pm_regions_after_flush = pm_regions_after_write.flush();
            assert forall |which_log: u32| #[trigger] log_index_trigger(which_log as int) && which_log < self.num_logs implies {
                let w = which_log as int;
                &&& metadata_consistent_with_info(pm_regions_after_flush[w], multilog_id, self.num_logs, which_log,
                                                 !self.cdb, self.infos@[w])
                &&& info_consistent_with_log_area(pm_regions_after_flush[w], self.infos@[w], self.state@[w])
                &&& metadata_types_set(pm_regions_after_flush.committed())
            } by {
                let w = which_log as int;
                lemma_establish_subrange_equivalence(
                    wrpm_regions@[which_log as int].committed(),
                    pm_regions_after_flush[which_log as int].committed());

                lemma_each_metadata_consistent_with_info_after_cdb_update(
                    wrpm_regions@,
                    pm_regions_after_flush,
                    multilog_id,
                    self.num_logs,
                    new_cdb_bytes,
                    !self.cdb,
                    self.infos@
                );

                assert(pm_regions_after_flush.len() == wrpm_regions@.len());
                lemma_metadata_types_set_after_cdb_update(wrpm_regions@, pm_regions_after_flush, multilog_id,
                                                          new_cdb_bytes, self.cdb);
            }
            assert(memory_matches_deserialized_cdb(pm_regions_after_flush, !self.cdb));

            // Show that if we crash after the write and flush, we recover
            // to an abstract state corresponding to `self.state@` after
            // dropping pending appends.

            proof {
                lemma_invariants_imply_crash_recover_forall(pm_regions_after_flush, multilog_id,
                                                            self.num_logs, !self.cdb, self.infos@, self.state@);
            }

            // Show that if we crash after initiating the write of the CDB,
            // we'll recover to a permissible state. There are two cases:
            //
            // If we crash without any updating, then we'll recover to
            // state `prev_state.drop_pending_appends()` with the current
            // CDB.
            //
            // If we crash after writing, then we'll recover to state
            // `self.state@.drop_pending_appends()` with the flipped CDB.
            //
            // Because we're only writing within the persistence
            // granularity of the persistent memory, a crash in the middle
            // will either leave the persistent memory in the pre-state or
            // the post-state.
            //
            // This means we're allowed to do the write because if we
            // crash, we'll either be in state wrpm_regions@.committed() or
            // pm_regions_after_write.flush().committed(). In the former
            // case, we'll be in state `prev_state.drop_pending_appends()`
            // and in the latter case, as shown above, we'll be in state
            // `self.state@.drop_pending_appends()`.

            assert forall |crash_bytes| pm_regions_after_write.can_crash_as(crash_bytes) implies
                       #[trigger] perm.check_permission(crash_bytes) by {
                lemma_invariants_imply_crash_recover_forall(wrpm_regions@, multilog_id, self.num_logs,
                                                            self.cdb, prev_infos, prev_state);
                lemma_single_write_crash_effect_on_pm_regions_view(wrpm_regions@, 0int,
                                                                   ABSOLUTE_POS_OF_LOG_CDB as int, new_cdb_bytes);
            }

            // Finally, update the CDB, then flush, then flip `self.cdb`.
            // There's no need to flip `self.cdb` atomically with the write
            // since the flip of `self.cdb` is happening in local
            // non-persistent memory so if we crash it'll be lost anyway.
            // wrpm_regions.write(0, ABSOLUTE_POS_OF_LOG_CDB, new_cdb.as_slice(), Tracked(perm));
            wrpm_regions.serialize_and_write(0, ABSOLUTE_POS_OF_LOG_CDB, &new_cdb, Tracked(perm));
            wrpm_regions.flush();
            self.cdb = !self.cdb;

            proof {
                lemma_if_no_outstanding_writes_then_persistent_memory_regions_view_can_only_crash_as_committed(
                    wrpm_regions@
                );
            }
        }

        fn update_inactive_log_metadata<PMRegions>(
            &mut self,
            wrpm_regions: &mut WriteRestrictedPersistentMemoryRegions<TrustedMultiLogPermission, PMRegions>,
            Ghost(multilog_id): Ghost<u128>,
            Ghost(prev_infos): Ghost<Seq<LogInfo>>,
            Ghost(prev_state): Ghost<AbstractMultiLogState>,
            Tracked(perm): Tracked<&TrustedMultiLogPermission>,
        )
            where
                PMRegions: PersistentMemoryRegions,
            requires
                old(wrpm_regions).inv(),
                memory_matches_deserialized_cdb(old(wrpm_regions)@, old(self).cdb),
                no_outstanding_writes_to_metadata(old(wrpm_regions)@),
                each_metadata_consistent_with_info(old(wrpm_regions)@, multilog_id, old(self).num_logs,
                                                   old(self).cdb, prev_infos),
                each_info_consistent_with_log_area(old(wrpm_regions)@.flush(), old(self).num_logs,
                                                old(self).infos@, old(self).state@),
                each_info_consistent_with_log_area(old(wrpm_regions)@, old(self).num_logs, prev_infos, prev_state),
                forall |which_log: int| #[trigger] log_index_trigger(which_log) && 0 <= which_log < old(self).num_logs ==>
                    old(self).infos@[which_log].log_area_len == prev_infos[which_log].log_area_len,
                forall |s| {
                          ||| Self::recover(s, multilog_id) == Some(prev_state.drop_pending_appends())
                          ||| Self::recover(s, multilog_id) == Some(old(self).state@.drop_pending_appends())
                      } ==> #[trigger] perm.check_permission(s),
                metadata_types_set(old(wrpm_regions)@.committed()),
                forall |i: int| #[trigger] log_index_trigger(i) && 0 <= i < old(wrpm_regions)@.len() ==>
                    ABSOLUTE_POS_OF_LOG_AREA < old(wrpm_regions)@[i].len(),
                old(wrpm_regions)@.len() > 0,
            ensures
                wrpm_regions.inv(),
                self.state == old(self).state,
                wrpm_regions.constants() == old(wrpm_regions).constants(),
                memory_matches_deserialized_cdb(wrpm_regions@, self.cdb),
                each_metadata_consistent_with_info(wrpm_regions@, multilog_id, self.num_logs, self.cdb, prev_infos),
                each_info_consistent_with_log_area(wrpm_regions@, self.num_logs, prev_infos, prev_state),
                each_info_consistent_with_log_area(wrpm_regions@.flush(), self.num_logs, self.infos@, self.state@),
                forall |s| Self::recover(s, multilog_id) == Some(prev_state.drop_pending_appends()) ==>
                    #[trigger] perm.check_permission(s),
                forall |i: int| #[trigger] log_index_trigger(i) && 0 <= i < self.num_logs ==>
                    self.infos@[i].log_area_len == prev_infos[i].log_area_len,
                forall |which_log: u32| #[trigger] log_index_trigger(which_log as int) && which_log < self.num_logs ==> {
                    let w = which_log as int;
                    let flushed = wrpm_regions@.flush();
                    metadata_consistent_with_info(flushed[w], multilog_id, self.num_logs, which_log,
                                                  !self.cdb, self.infos@[w])
                },
                no_outstanding_writes_to_active_metadata(wrpm_regions@, self.cdb),
                metadata_types_set(wrpm_regions@.committed()),
                active_metadata_is_equal(old(wrpm_regions)@, wrpm_regions@),
                forall |i: int| #[trigger] log_index_trigger(i) && 0 <= i < wrpm_regions@.len() ==>
                    wrpm_regions@[i].len() == old(wrpm_regions)@[i].len(),
                forall |i: int| #[trigger] log_index_trigger(i) && 0 <= i < wrpm_regions@.len() ==>
                    ABSOLUTE_POS_OF_LOG_AREA < wrpm_regions@[i].len(),
                forall |i: int| #[trigger] log_index_trigger(i) && 0 <= i < wrpm_regions@.len() ==>
                    inactive_metadata_types_set_in_region(wrpm_regions@.flush().committed()[i], self.cdb),
                wrpm_regions@.len() > 0,
                
        {
            broadcast use pmcopy_axioms;
            proof {
                lemma_metadata_sizes();
            }

            let unused_metadata_pos = if self.cdb { ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE }
                                            else { ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_TRUE };
            assert(unused_metadata_pos == get_log_metadata_pos(!self.cdb));
            assert(log_index_trigger(0));

            let ghost old_wrpm_regions = wrpm_regions@;
            proof {
                // Before we enter the loop, we need to prove that there are no outstanding writes to active
                // metadata to satisfy the invariant. This follows from the fact that there are no outstanding 
                // writes to *any* metadata, but Z3 needs a hint from the lemma.
                lemma_no_outstanding_writes_to_metadata_implies_no_outstanding_writes_to_active_metadata(
                    wrpm_regions@, self.cdb);
            }

            let ghost old_prev_infos = prev_infos;
            let ghost old_prev_state = prev_state;

            for current_log in 0..self.num_logs
                invariant
                    wrpm_regions.inv(),
                    wrpm_regions.constants() == old(wrpm_regions).constants(),
                    unused_metadata_pos == get_log_metadata_pos(!self.cdb),
                    memory_matches_deserialized_cdb(wrpm_regions@, self.cdb),
                    each_metadata_consistent_with_info(wrpm_regions@, multilog_id, self.num_logs, self.cdb, prev_infos),
                    each_info_consistent_with_log_area(wrpm_regions@, self.num_logs, prev_infos, prev_state),
                    each_info_consistent_with_log_area(wrpm_regions@.flush(), self.num_logs, self.infos@, self.state@),
                    forall |s| Self::recover(s, multilog_id) == Some(prev_state.drop_pending_appends()) ==>
                        #[trigger] perm.check_permission(s),
                    forall |which_log: int| #[trigger] log_index_trigger(which_log) && 0 <= which_log < self.num_logs ==>
                        self.infos@[which_log].log_area_len == prev_infos[which_log].log_area_len,

                    // For logs we haven't updated the metadata for
                    // yet, there are still no outstanding writes in
                    // the inactive metadata part, and the region's
                    // contents are unchanged since the beginning of
                    // this function.

                    forall |which_log: int|
                        #[trigger] log_index_trigger(which_log) && current_log <= which_log < self.num_logs ==>
                        wrpm_regions@[which_log].no_outstanding_writes_in_range(
                            unused_metadata_pos as int,
                            unused_metadata_pos + LogMetadata::spec_size_of() + u64::spec_size_of()),
                    forall |which_log: int|
                        #[trigger] log_index_trigger(which_log) && current_log <= which_log < self.num_logs ==> {
                        wrpm_regions@[which_log] == old(wrpm_regions)@[which_log]
                    },

                    // For logs that we *have* updated the metadata
                    // for, we've made the metadata corresponding to
                    // !self.cdb consistent with self.infos@.

                    forall |which_log: u32| #[trigger] log_index_trigger(which_log as int) && which_log < current_log ==> {
                        let w = which_log as int;
                        let flushed = wrpm_regions@.flush();
                        metadata_consistent_with_info(flushed[w], multilog_id, self.num_logs, which_log,
                                                      !self.cdb, self.infos@[w])
                    },

                    // Despite potential updates to each log, their active metadata is never 
                    // modified by the loop.

                    no_outstanding_writes_to_active_metadata(wrpm_regions@, self.cdb),
                    metadata_types_set(wrpm_regions@.committed()),
                    active_metadata_is_equal(old_wrpm_regions, wrpm_regions@),

                    // The loop does not change the size of any of the regions
                    forall |i: int| #[trigger] log_index_trigger(i) && 0 <= i < wrpm_regions@.len() ==>
                        wrpm_regions@[i].len() == old(wrpm_regions)@[i].len(),
                    forall |i: int| #[trigger] log_index_trigger(i) && 0 <= i < wrpm_regions@.len() ==>
                        ABSOLUTE_POS_OF_LOG_AREA < wrpm_regions@[i].len(),
                    forall |i: int| #[trigger] log_index_trigger(i) && 0 <= i < current_log ==>
                        inactive_metadata_types_set_in_region(wrpm_regions@.flush().committed()[i], self.cdb),
                    wrpm_regions@.len() > 0,

                    self.cdb == old(self).cdb,
                    prev_infos == old_prev_infos,
                    prev_state == old_prev_state,
            {
                broadcast use pmcopy_axioms; // Remove this workaround once https://github.com/verus-lang/verus/issues/1166 is fixed
                reveal(spec_padding_needed);
                // proof {
                //     lemma_metadata_sizes();
                // }

                assert(log_index_trigger(current_log as int));
                let ghost cur = current_log as int;

                // Encode the log metadata as bytes, and compute the CRC of those bytes

                let info = &self.infos[current_log as usize];
                let log_metadata = LogMetadata {
                    head: info.head,
                    _padding: 0,
                    log_length: info.log_length
                };
                let log_crc = calculate_crc(&log_metadata);

                let ghost log_metadata_bytes = log_metadata.spec_to_bytes();
                let ghost log_crc_bytes = log_crc.spec_to_bytes();

                // Prove that updating the inactive metadata+CRC maintains
                // all invariants that held before. We prove this separately
                // for metadata and CRC because they are updated in two separate
                // writes.

                proof {
                    lemma_updating_inactive_metadata_maintains_invariants(
                        wrpm_regions@, multilog_id, self.num_logs, self.cdb, prev_infos, prev_state, current_log,
                        log_metadata_bytes);

                    let wrpm_regions_new = wrpm_regions@.write(cur, unused_metadata_pos as int, log_metadata_bytes);
                    lemma_updating_inactive_crc_maintains_invariants(
                        wrpm_regions_new, multilog_id, self.num_logs, self.cdb, prev_infos, prev_state, current_log,
                        log_crc_bytes);
                }

                let ghost wrpm_regions_new = wrpm_regions@.write(cur, unused_metadata_pos as int, log_metadata_bytes);
                proof {
                    // The proofs in this block apply to both the crash case and the regular case, and help us prove
                    // that the metadata types are still set after the write regardless of whether it completes or not.
                    assert(forall |i: int| #[trigger] log_index_trigger(i) && 0 <= i < wrpm_regions_new.len() && i != cur ==> 
                        wrpm_regions@[i] == wrpm_regions_new[i]); 
                    lemma_write_to_inactive_metadata_implies_active_metadata_stays_equal(
                        wrpm_regions@, wrpm_regions_new, 
                        cur, unused_metadata_pos as int, log_metadata_bytes, self.cdb
                    );
                }

                // Use `lemma_invariants_imply_crash_recover_forall` to prove that it's OK to call
                // `write`. (One of the conditions for calling that lemma is that our invariants
                // hold, which we just proved above.)
                assert forall |crash_bytes| wrpm_regions_new.can_crash_as(crash_bytes)
                           implies #[trigger] perm.check_permission(crash_bytes) by {
                    lemma_invariants_imply_crash_recover_forall(
                        wrpm_regions_new, multilog_id, self.num_logs, self.cdb, prev_infos, prev_state);

                    lemma_metadata_set_after_crash(wrpm_regions_new, self.cdb);
                    assert(metadata_types_set(crash_bytes));
                }

                // Write the new metadata to the inactive header (without the CRC)
                let ghost old_wrpm_regions = wrpm_regions@;
                
                wrpm_regions.serialize_and_write(current_log as usize, unused_metadata_pos, &log_metadata,
                                                 Tracked(perm));

                // Now prove that the CRC is safe to update as well, and write it.

                let ghost wrpm_regions_new =
                    wrpm_regions@.write(cur, unused_metadata_pos + LogMetadata::spec_size_of(), log_crc_bytes);
                proof {
                    // Prove that there are no outstanding writes to active metadata in any of the logs
                    assert(forall |i: int| #[trigger] log_index_trigger(i) && 0 <= i < wrpm_regions_new.len() && i != cur ==> 
                        wrpm_regions@[i] == wrpm_regions_new[i]); 

                    lemma_write_to_inactive_metadata_implies_active_metadata_stays_equal(
                        wrpm_regions@, wrpm_regions_new, 
                        cur, unused_metadata_pos + LogMetadata::spec_size_of(), log_crc_bytes, self.cdb
                    );

                    // after this write, the inactive CRC will be set
                    assert(wrpm_regions_new[cur].flush().committed().subrange(
                        unused_metadata_pos + LogMetadata::spec_size_of(), 
                        unused_metadata_pos + LogMetadata::spec_size_of() + u64::spec_size_of()
                    ) == log_crc_bytes);
                }

                assert forall |crash_bytes| wrpm_regions_new.can_crash_as(crash_bytes)
                           implies #[trigger] perm.check_permission(crash_bytes) by {
                    lemma_invariants_imply_crash_recover_forall(
                        wrpm_regions_new, multilog_id, self.num_logs, self.cdb, prev_infos, prev_state);

                    lemma_metadata_set_after_crash(wrpm_regions_new, self.cdb);
                    assert(metadata_types_set(crash_bytes));
                }

                wrpm_regions.serialize_and_write(
                    current_log as usize, unused_metadata_pos + size_of::<LogMetadata>() as u64,
                    &log_crc, Tracked(perm)
                );
                
                // Prove that after the flush, the log metadata corresponding to the unused CDB will
                // be reflected in memory.

                let ghost flushed = wrpm_regions_new.flush();
                assert (metadata_consistent_with_info(flushed[current_log as int], multilog_id,
                                                      self.num_logs, current_log, !self.cdb, self.infos@[cur])) by {
                    let mem1 = wrpm_regions@[cur].committed();
                    let mem2 = flushed[cur].committed();
                    lemma_establish_subrange_equivalence(mem1, mem2);
                    lemma_write_reflected_after_flush_committed(wrpm_regions@[cur], unused_metadata_pos as int,
                                                                log_metadata_bytes + log_crc_bytes);
                    assert(extract_log_metadata(mem2, !self.cdb) =~= log_metadata_bytes);
                    assert(extract_log_crc(mem2, !self.cdb) =~= log_crc_bytes);
                    assert(deserialize_log_metadata(mem2, !self.cdb) == log_metadata);
                    assert(deserialize_log_crc(mem2, !self.cdb) == log_crc);
                }

                assert(wrpm_regions@.flush().committed()[cur].subrange(
                           unused_metadata_pos as int,
                           unused_metadata_pos + LogMetadata::spec_size_of()
                       ) == log_metadata.spec_to_bytes());
            }
        }

        // The `commit` method commits all tentative appends that have been
        // performed since the last one. See `README.md` for more
        // documentation and examples of its use.
        //
        // This method is passed a write-restricted collection of
        // persistent memory regions `wrpm_regions`. This restricts
        // how it can write `wrpm_regions`. It's only given permission
        // (in `perm`) to write if it can prove that any crash after
        // initiating the write is safe. That is, any such crash must
        // put the memory in a state that recovers as either (1) the
        // current abstract state with all pending appends dropped, or
        // (2) the abstract state after all pending appends are
        // committed.
        pub exec fn commit<PMRegions>(
            &mut self,
            wrpm_regions: &mut WriteRestrictedPersistentMemoryRegions<TrustedMultiLogPermission, PMRegions>,
            Ghost(multilog_id): Ghost<u128>,
            Tracked(perm): Tracked<&TrustedMultiLogPermission>,
        ) -> (result: Result<(), MultiLogErr>)
            where
                PMRegions: PersistentMemoryRegions
            requires
                old(self).inv(&*old(wrpm_regions), multilog_id),
                forall |s| #[trigger] perm.check_permission(s) <==> {
                    ||| Self::recover(s, multilog_id) == Some(old(self)@.drop_pending_appends())
                    ||| Self::recover(s, multilog_id) == Some(old(self)@.commit().drop_pending_appends())
                },
            ensures
                self.inv(wrpm_regions, multilog_id),
                wrpm_regions.constants() == old(wrpm_regions).constants(),
                can_only_crash_as_state(wrpm_regions@, multilog_id, self@.drop_pending_appends()),
                result is Ok,
                self@ == old(self)@.commit(),
        {
            let ghost prev_infos = self.infos@;
            let ghost prev_state = self.state@;

            self.state = Ghost(self.state@.commit());

            // Loop, where `current_log` ranges through the log indices,
            // each time updating `self.infos[current_log]`. Each iteration
            // maintains the invariants that (1) the persistent memory is
            // compatible with `prev_infos` and `prev_state`, and (2) for
            // each log we've already updated, the persistent memory's log
            // area, if flushed, would be consistent with `self.infos` and
            // `self.state`.

            for current_log in iter: 0..self.num_logs
                invariant
                    iter.end == self.num_logs, // we need to remember this since `self` is changed in the loop body
                    wrpm_regions.inv(),

                    memory_matches_deserialized_cdb(wrpm_regions@, self.cdb),
                    each_metadata_consistent_with_info(wrpm_regions@, multilog_id, self.num_logs, self.cdb, prev_infos),
                    each_info_consistent_with_log_area(wrpm_regions@, self.num_logs, prev_infos, prev_state),
                    self.infos@.len() == self.state@.num_logs() == self.num_logs,
                    self.state@ == prev_state.commit(),

                    forall |which_log: u32| #[trigger] log_index_trigger(which_log as int) && which_log < self.num_logs ==> {
                        let w = which_log as int;
                        if which_log < current_log {
                            info_consistent_with_log_area(wrpm_regions@.flush()[w], self.infos[w], self.state@[w])
                        }
                        else {
                            self.infos[w] == prev_infos[w]
                        }
                    },
            {
                assert(log_index_trigger(current_log as int)); // trigger various useful foralls in invariants

                // Update the `current_log`th entry in `self.infos` to
                // update the `log_length` field to be whatever is
                // currently in `log_plus_pending_length`. Verus currently
                // doesn't support updating a field of an element of a
                // vector, so we have to update the entire element. We must
                // furthermore use Verus's vector `set` method for this
                // because Verus doesn't support vector elements as
                // left-hand sides of assignments.

                let new_log_length = self.infos[current_log as usize].log_plus_pending_length;
                let new_info = LogInfo{
                    log_length: new_log_length,
                    ..self.infos[current_log as usize]
                };
                self.infos.set(current_log as usize, new_info);
            }

            // Update the inactive metadata on all regions and flush, then
            // swap the CDB to its opposite.

            self.update_log_metadata(wrpm_regions, Ghost(multilog_id), Ghost(prev_infos),
                                        Ghost(prev_state), Tracked(perm));

            Ok(())
        }

        // The `advance_head` method advances the head of one of the logs,
        // thereby making more space for appending but making log entries
        // before the new head unavailable for reading. Upon return from
        // this method, the head advancement is durable, i.e., it will
        // survive crashes. See `README.md` for more documentation and
        // examples of its use.
        //
        // This method is passed a write-restricted collection of
        // persistent memory regions `wrpm_regions`. This restricts how it
        // can write `wrpm_regions`. It's only given permission (in `perm`)
        // to write if it can prove that any crash after initiating the
        // write is safe. That is, any such crash must put the memory in a
        // state that recovers as either (1) the current abstract state
        // with all pending appends dropped, or (2) the state after
        // advancing the head and then dropping all pending appends.
        pub exec fn advance_head<PMRegions>(
            &mut self,
            wrpm_regions: &mut WriteRestrictedPersistentMemoryRegions<TrustedMultiLogPermission, PMRegions>,
            which_log: u32,
            new_head: u128,
            Ghost(multilog_id): Ghost<u128>,
            Tracked(perm): Tracked<&TrustedMultiLogPermission>,
        ) -> (result: Result<(), MultiLogErr>)
            where
                PMRegions: PersistentMemoryRegions
            requires
                old(self).inv(&*old(wrpm_regions), multilog_id),
                forall |s| #[trigger] perm.check_permission(s) <==> {
                    ||| Self::recover(s, multilog_id) == Some(old(self)@.drop_pending_appends())
                    ||| Self::recover(s, multilog_id) ==
                        Some(old(self)@.advance_head(which_log as int, new_head as int).drop_pending_appends())
                },
            ensures
                self.inv(wrpm_regions, multilog_id),
                wrpm_regions.constants() == old(wrpm_regions).constants(),
                can_only_crash_as_state(wrpm_regions@, multilog_id, self@.drop_pending_appends()),
                match result {
                    Ok(()) => {
                        let w = which_log as int;
                        &&& which_log < self@.num_logs()
                        &&& old(self)@[w].head <= new_head <= old(self)@[w].head + old(self)@[w].log.len()
                        &&& self@ == old(self)@.advance_head(w, new_head as int)
                    },
                    Err(MultiLogErr::InvalidLogIndex{ }) => {
                        &&& self@ == old(self)@
                        &&& which_log >= self@.num_logs()
                    },
                    Err(MultiLogErr::CantAdvanceHeadPositionBeforeHead { head }) => {
                        &&& self@ == old(self)@
                        &&& which_log < self@.num_logs()
                        &&& head == self@[which_log as int].head
                        &&& new_head < head
                    },
                    Err(MultiLogErr::CantAdvanceHeadPositionBeyondTail { tail }) => {
                        &&& self@ == old(self)@
                        &&& which_log < self@.num_logs()
                        &&& tail == self@[which_log as int].head + self@[which_log as int].log.len()
                        &&& new_head > tail
                    },
                    _ => false
                }
        {
            // Even if we return an error code, we still have to prove that
            // upon return the states we can crash into recover into valid
            // abstract states.

            proof {
                assert(log_index_trigger(0));
                lemma_invariants_imply_crash_recover_forall(wrpm_regions@, multilog_id, self.num_logs, self.cdb,
                                                            self.infos@, self.state@);
            }

            // Handle error cases due to improper parameters passed to the
            // function.

            if which_log >= self.num_logs {
                return Err(MultiLogErr::InvalidLogIndex{ });
            }

            assert(log_index_trigger(which_log as int)); // trigger useful foralls in invariants
            let info = &self.infos[which_log as usize];
            if new_head < info.head {
                return Err(MultiLogErr::CantAdvanceHeadPositionBeforeHead{ head: info.head })
            }
            if new_head - info.head > info.log_length as u128 {
                return Err(MultiLogErr::CantAdvanceHeadPositionBeyondTail{ tail: info.head + info.log_length as u128 })
            }

            // To compute the new head mod n (where n is the log area
            // length), take the old head mod n, add the amount by
            // which the head is advancing, then subtract n if
            // necessary.

            let amount_of_advancement: u64 = (new_head - info.head) as u64;
            let new_head_log_area_offset =
                if amount_of_advancement < info.log_area_len - info.head_log_area_offset {
                    amount_of_advancement + info.head_log_area_offset
                }
                else {
                    // To compute `info.head_log_area_offset` [the old
                    // head] plus `amount_of_advancement` [the amount
                    // by which the head is advancing] minus
                    // `info.log_area_len` [the log area length], we
                    // do it in the following order that guarantees no
                    // overflow/underflow.
                    amount_of_advancement - (info.log_area_len - info.head_log_area_offset)
                };

            assert(new_head_log_area_offset == new_head as int % info.log_area_len as int) by {
                // Here's a mathematical proof that doing the above
                // calculation of `new_head_log_area_offset` achieves the
                // desired computation of `new_head % log_area_len`.

                let n = info.log_area_len as int;
                let advancement = amount_of_advancement as int;
                let head = info.head as int;
                let head_mod_n = info.head_log_area_offset as int;
                let supposed_new_head_mod_n = new_head_log_area_offset as int;

                // First, observe that `advancement` plus `head` is
                // congruent modulo n to `advancement` plus `head` % n.

                assert((advancement + head) % n == (advancement + head_mod_n) % n) by {
                    assert(head == n * (head / n) + head % n) by {
                        lemma_fundamental_div_mod(head, n);
                    }
                    assert((n * (head / n) + (advancement + head_mod_n)) % n == (advancement + head_mod_n) % n) by {
                        lemma_mod_multiples_vanish(head / n, advancement + head_mod_n, n);
                    }
                }

                // Next, observe that `advancement` + `head` % n is
                // congruent modulo n to itself minus n. This is
                // relevant because there are two cases for computing
                // `new_head_mod_log_area_offset`. In one case, it's
                // computed as `advancement` + `head` % n. In the
                // other case, it's that quantity minus n.

                assert((advancement + head % n) % n == (advancement + head_mod_n - n) % n) by {
                    lemma_mod_sub_multiples_vanish(advancement + head_mod_n, n);
                }

                // So we know that in either case, `new_head` % n ==
                // `new_head_mod_log_area_offset` % n.

                assert(new_head as int % n == supposed_new_head_mod_n % n);

                // But what we want to prove is that `new_head` % n ==
                // `new_head_mod_log_area_offset`. So we need to show
                // that `new_head_mod_log_area_offset` % n ==
                // `new_head_mod_log_area_offset`.  We can deduce this
                // from the fact that 0 <= `new_head_mod_log_area_offset`
                // < n.

                assert(supposed_new_head_mod_n % n == supposed_new_head_mod_n) by {
                    lemma_small_mod(supposed_new_head_mod_n as nat, n as nat);
                }
            }

            // Update the `which_log`th entry in `self.infos` to reflect
            // the change to the head position. This necessitates updating
            // all the fields except the log area length. We have to use
            // Verus's vector `set` method for this because Verus doesn't
            // support vector elements as left-hand sides of assignments.

            let ghost prev_infos = self.infos@;
            let new_info = LogInfo{
                log_area_len: info.log_area_len,
                head: new_head,
                head_log_area_offset: new_head_log_area_offset,
                log_length: info.log_length - amount_of_advancement,
                log_plus_pending_length: info.log_plus_pending_length - amount_of_advancement,
            };
            self.infos.set(which_log as usize, new_info);

            // Update the abstract `self.state` to reflect the head update.

            let ghost prev_state = self.state@;
            self.state = Ghost(self.state@.advance_head(which_log as int, new_head as int));

            // To prove that the log area for log number `which_log` is
            // compatible with the new `self.infos` and `self.state`, we
            // need to reason about how addresses in the log area
            // correspond to relative log positions. That's because the
            // invariants we know about the log area talk about log
            // positions relative to the old head, but we want to know
            // things about log positions relative to the new head. What
            // connects those together is that they both talk about the
            // same addresses in the log area.

            let ghost w = which_log as int;
            let ghost flushed_regions = wrpm_regions@.flush();
            assert (info_consistent_with_log_area(flushed_regions[w], self.infos@[w], self.state@[w])) by {
                lemma_addresses_in_log_area_correspond_to_relative_log_positions(wrpm_regions@[w], prev_infos[w]);
            }

            // Update the inactive metadata on all regions and flush, then
            // swap the CDB to its opposite. We have to update the metadata
            // on all regions, even though we're only advancing the head on
            // one, for the following reason. The only way available to us
            // to update the active metadata is to flip the CDB, but this
            // flips which metadata is active on *all* regions. So we have
            // to update the inactive metadata on all regions.

            self.update_log_metadata(wrpm_regions, Ghost(multilog_id), Ghost(prev_infos), Ghost(prev_state),
                                        Tracked(perm));

            Ok(())
        }

        // This local helper method proves that we can read a portion of
        // the abstract log by reading a continuous range of the log area.
        // It requires that the position being read from is correct, and
        // that the read is short enough to not require wrapping around the
        // end of the log area.
        proof fn lemma_read_of_continuous_range(
            &self,
            pm_regions_view: PersistentMemoryRegionsView,
            multilog_id: u128,
            which_log: u32,
            pos: int,
            len: int,
            addr: int,
        )
            requires
                log_index_trigger(which_log as int),
                which_log < self.num_logs,
                len > 0,
                each_metadata_consistent_with_info(pm_regions_view, multilog_id, self.num_logs, self.cdb, self.infos@),
                each_info_consistent_with_log_area(pm_regions_view, self.num_logs, self.infos@, self.state@),
                ({
                    let info = self.infos@[which_log as int];
                    let max_len_without_wrapping = info.log_area_len -
                        relative_log_pos_to_log_area_offset(pos - info.head,
                                                            info.head_log_area_offset as int,
                                                            info.log_area_len as int);
                    &&& pos >= info.head
                    &&& pos + len <= info.head + info.log_length
                    &&& len <= max_len_without_wrapping
                    &&& addr == ABSOLUTE_POS_OF_LOG_AREA +
                           relative_log_pos_to_log_area_offset(pos - info.head as int,
                                                               info.head_log_area_offset as int,
                                                               info.log_area_len as int)
                })
            ensures
                ({
                    let log = self@[which_log as int];
                    let pm_region_view = pm_regions_view[which_log as int];
                    &&& pm_region_view.no_outstanding_writes_in_range(addr, addr + len)
                    &&& pm_region_view.committed().subrange(addr, addr + len)
                           == log.log.subrange(pos - log.head, pos + len - log.head)
                })
        {
            let w = which_log as int;
            let info = self.infos@[w];
            let s = self.state@[w];
            let pm_region_view = pm_regions_view[w];

            // The key to the proof is that we need to reason about how
            // addresses in the log area correspond to relative log
            // positions. This is because the invariant talks about
            // relative log positions but this lemma is proving things
            // about addresses in the log area.

            lemma_addresses_in_log_area_correspond_to_relative_log_positions(pm_region_view, info);
            assert(pm_region_view.committed().subrange(addr, addr + len) =~=
                   s.log.subrange(pos - s.head, pos + len - s.head));
        }

        // The `read` method reads part of one of the logs, returning a
        // vector containing the read bytes. It doesn't guarantee that
        // those bytes aren't corrupted by persistent memory corruption.
        // See `README.md` for more documentation and examples of its use.
        pub exec fn read<Perm, PMRegions>(
            &self,
            wrpm_regions: &WriteRestrictedPersistentMemoryRegions<Perm, PMRegions>,
            which_log: u32,
            pos: u128,
            len: u64,
            Ghost(multilog_id): Ghost<u128>,
        ) -> (result: Result<Vec<u8>, MultiLogErr>)
            where
                Perm: CheckPermission<Seq<Seq<u8>>>,
                PMRegions: PersistentMemoryRegions
            requires
                self.inv(wrpm_regions, multilog_id),
                pos + len <= u128::MAX
            ensures
                ({
                    let log = self@[which_log as int];
                    match result {
                        Ok(bytes) => {
                            let true_bytes = self@.read(which_log as int, pos as int, len as int);
                            &&& which_log < self@.num_logs()
                            &&& pos >= log.head
                            &&& pos + len <= log.head + log.log.len()
                            &&& read_correct_modulo_corruption(bytes@, true_bytes,
                                                              wrpm_regions.constants().impervious_to_corruption)
                        },
                        Err(MultiLogErr::InvalidLogIndex{ }) => {
                            which_log >= self@.num_logs()
                        },
                        Err(MultiLogErr::CantReadBeforeHead{ head: head_pos }) => {
                            &&& which_log < self@.num_logs()
                            &&& pos < log.head
                            &&& head_pos == log.head
                        },
                        Err(MultiLogErr::CantReadPastTail{ tail }) => {
                            &&& which_log < self@.num_logs()
                            &&& pos + len > log.head + log.log.len()
                            &&& tail == log.head + log.log.len()
                        },
                        _ => false,
                    }
                })
        {
            // Handle error cases due to improper parameters passed to the
            // function.

            if which_log >= self.num_logs {
                return Err(MultiLogErr::InvalidLogIndex{ });
            }

            assert(log_index_trigger(which_log as int)); // triggers useful foralls in invariants

            let info = &self.infos[which_log as usize];
            if pos < info.head {
                return Err(MultiLogErr::CantReadBeforeHead{ head: info.head })
            }
            if len > info.log_length { // We have to do this check first to avoid underflow in the next comparison
                return Err(MultiLogErr::CantReadPastTail{ tail: info.head + info.log_length as u128 })
            }
            if pos - info.head > (info.log_length - len) as u128 { // we know `info.log_length - len` can't underflow
                return Err(MultiLogErr::CantReadPastTail{ tail: info.head + info.log_length as u128 })
            }

            let ghost s = self.state@[which_log as int];
            let ghost true_bytes = s.log.subrange(pos - s.head, pos + len - s.head);

            if len == 0 {
                // Case 0: The trivial case where we're being asked to read zero bytes.

                assert (true_bytes =~= Seq::<u8>::empty());
                assert (maybe_corrupted(Seq::<u8>::empty(), true_bytes, Seq::<int>::empty()));
                return Ok(Vec::<u8>::new());
            }

            let pm_regions = wrpm_regions.get_pm_regions_ref();

            let log_area_len: u64 = self.infos[which_log as usize].log_area_len;
            let relative_pos: u64 = (pos - info.head) as u64;
            if relative_pos >= log_area_len - info.head_log_area_offset {

                // Case 1: The position we're being asked to read appears
                // in the log area before the log head. So the read doesn't
                // need to wrap.
                //
                // We could compute the address to write to with:
                //
                // `write_addr = ABSOLUTE_POS_OF_LOG_AREA + pos % info.log_area_len;`
                //
                // But we can replace the expensive modulo operation above with two subtraction
                // operations as follows. This is somewhat subtle, but we have verification backing
                // us up and proving this optimization correct.

                let addr = ABSOLUTE_POS_OF_LOG_AREA + relative_pos - (info.log_area_len - info.head_log_area_offset);
                proof { self.lemma_read_of_continuous_range(pm_regions@, multilog_id, which_log, pos as int,
                                                            len as int, addr as int); }
                let bytes = match pm_regions.read_unaligned(which_log as usize, addr, len) {
                    Ok(bytes) => bytes,
                    Err(e) => {
                        assert(false);
                        return Err(MultiLogErr::PmemErr { err: e });
                    }
                };
                return Ok(bytes);
            }

            // The log area wraps past the point we're reading from, so we
            // need to compute the maximum length we can read without
            // wrapping to be able to figure out whether we need to wrap.

            let max_len_without_wrapping: u64 = log_area_len - info.head_log_area_offset - relative_pos;
            assert(max_len_without_wrapping == info.log_area_len -
                   relative_log_pos_to_log_area_offset(pos - info.head,
                                                       info.head_log_area_offset as int, info.log_area_len as int));

            // Whether we need to wrap or not, we know the address where
            // our read should start, so we can compute that and put it in
            // `addr`.
            //
            // We could compute the address to write to with:
            //
            // `write_addr = ABSOLUTE_POS_OF_LOG_AREA + pos % info.log_area_len;`
            //
            // But we can replace the expensive modulo operation above with
            // one addition operation as follows. This is somewhat subtle,
            // but we have verification backing us up and proving this
            // optimization correct.

            let addr: u64 = ABSOLUTE_POS_OF_LOG_AREA + relative_pos + info.head_log_area_offset;
            assert(addr == ABSOLUTE_POS_OF_LOG_AREA +
                   relative_log_pos_to_log_area_offset(pos - info.head,
                                                       info.head_log_area_offset as int,
                                                       info.log_area_len as int));

            if len <= max_len_without_wrapping {

                // Case 2: We're reading few enough bytes that we don't have to wrap.

                proof { self.lemma_read_of_continuous_range(pm_regions@, multilog_id, which_log, pos as int,
                                                            len as int, addr as int); }
                let bytes = match pm_regions.read_unaligned(which_log as usize, addr, len) {
                    Ok(bytes) => bytes,
                    Err(e) => {
                        assert(false);
                        return Err(MultiLogErr::PmemErr { err: e });
                    }
                };
                return Ok(bytes);
            }

            // Case 3: We're reading enough bytes that we have to wrap.
            // That necessitates doing two contiguous reads, one from the
            // end of the log area and one from the beginning, and
            // concatenating the results.

            proof {
                self.lemma_read_of_continuous_range(pm_regions@, multilog_id, which_log, pos as int,
                                                    max_len_without_wrapping as int, addr as int);
            }

            let mut part1 = match pm_regions.read_unaligned(which_log as usize, addr, max_len_without_wrapping) {
                Ok(bytes) => bytes,
                Err(e) => {
                    assert(false);
                    return Err(MultiLogErr::PmemErr { err: e });
                }
            };

            proof {
                self.lemma_read_of_continuous_range(pm_regions@, multilog_id, which_log,
                                                    pos + max_len_without_wrapping,
                                                    len - max_len_without_wrapping,
                                                    ABSOLUTE_POS_OF_LOG_AREA as int);
            }

            let mut part2 = match pm_regions.read_unaligned(which_log as usize, ABSOLUTE_POS_OF_LOG_AREA,
                                                            len - max_len_without_wrapping) {
                Ok(bytes) => bytes,
                Err(e) => {
                    assert(false);
                    return Err(MultiLogErr::PmemErr { err: e });
                }
            };

            // Now, prove that concatenating them produces the correct
            // bytes to return. The subtle thing in this argument is that
            // the bytes are only correct modulo corruption. And the
            // "correct modulo corruption" specification function talks
            // about the concrete addresses the bytes were read from and
            // demands that those addresses all be distinct.

            proof {
                let true_part1 = s.log.subrange(pos - s.head, pos + max_len_without_wrapping - s.head);
                let true_part2 = s.log.subrange(pos + max_len_without_wrapping - s.head, pos + len - s.head);
                let addrs1 = Seq::<int>::new(max_len_without_wrapping as nat, |i: int| i + addr);
                let addrs2 = Seq::<int>::new((len - max_len_without_wrapping) as nat,
                                           |i: int| i + ABSOLUTE_POS_OF_LOG_AREA);
                assert(true_part1 + true_part2 =~= s.log.subrange(pos - s.head, pos + len - s.head));

                if !pm_regions.constants().impervious_to_corruption {
                    assert(maybe_corrupted(part1@ + part2@, true_part1 + true_part2, addrs1 + addrs2));
                    assert(all_elements_unique(addrs1 + addrs2));
                }
            }

            // Append the two byte vectors together and return the result.

            part1.append(&mut part2);
            Ok(part1)
        }

        // The `get_head_tail_and_capacity` method returns the head, tail,
        // and capacity of one of the logs. See `README.md` for more
        // documentation and examples of its use.
        #[allow(unused_variables)]
        pub exec fn get_head_tail_and_capacity<Perm, PMRegions>(
            &self,
            wrpm_regions: &WriteRestrictedPersistentMemoryRegions<Perm, PMRegions>,
            which_log: u32,
            Ghost(multilog_id): Ghost<u128>,
        ) -> (result: Result<(u128, u128, u64), MultiLogErr>)
            where
                Perm: CheckPermission<Seq<Seq<u8>>>,
                PMRegions: PersistentMemoryRegions
            requires
                self.inv(wrpm_regions, multilog_id)
            ensures
                ({
                    let log = self@[which_log as int];
                    match result {
                        Ok((result_head, result_tail, result_capacity)) => {
                            &&& which_log < self@.num_logs()
                            &&& result_head == log.head
                            &&& result_tail == log.head + log.log.len()
                            &&& result_capacity == log.capacity
                        },
                        Err(MultiLogErr::InvalidLogIndex{ }) => {
                            which_log >= self@.num_logs()
                        },
                        _ => false
                    }
                })
        {
            // Check for an invalid `which_log` parameter.

            if which_log >= self.num_logs {
                return Err(MultiLogErr::InvalidLogIndex{ });
            }

            let ghost w = which_log as int;
            assert(log_index_trigger(which_log as int)); // triggers useful foralls in invariants

            // We cache information in `self.infos` that lets us easily
            // compute the return values.

            let info = &self.infos[which_log as usize];
            Ok((info.head, info.head + info.log_length as u128, info.log_area_len))
        }
    }

}
