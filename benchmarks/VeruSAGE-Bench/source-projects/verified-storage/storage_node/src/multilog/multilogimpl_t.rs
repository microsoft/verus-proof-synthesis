//! This file contains the trusted implementation of a `MultiLogImpl`.
//! Although the verifier is run on this file, it needs to be
//! carefully read and audited to be confident of the correctness of
//! this multilog implementation.
//!
//! Fortunately, it delegates most of its work to an untrusted struct
//! `UntrustedMultiLogImpl`, which doesn't need to be read or audited.
//! It forces the `UntrustedMultiLogImpl` to satisfy certain
//! postconditions, and also places restrictions on what
//! `UntrustedMultiLogImpl` can do to persistent memory. These
//! restrictions ensure that even if the system or process crashes in
//! the middle of an operation, the system will still recover to a
//! consistent state.
//!
//! It requires `UntrustedMultiLogImpl` to implement routines that do the
//! various multilog operations like read and commit.
//!
//! It also requires `UntrustedMultiLogImpl` to provide a function
//! `UntrustedMultiLogImpl::recover`, which specifies what its `start`
//! routine will do to recover after a crash. It requires its `start`
//! routine to satisfy that specification. It also uses it to limit
//! how `UntrustedMultiLogImpl` writes to memory: It can only perform
//! updates that, if incompletely performed before a crash, still
//! leave the system in a valid state. The `recover` function takes a
//! second parameter, the `multilog_id` which is passed to the start
//! routine.
//!
//! It also requires `UntrustedMultiLogImpl` to provide a function `view`
//! that converts the current state into an abstract log. It requires that
//! performing a certain operation on the `UntrustedMultiLogImpl` causes a
//! corresponding update to its abstract view. For instance, calling
//! the `u.commit()` method should cause the resulting `u.view()` to
//! become `old(u).view().commit()`.
//!
//! It also permits `UntrustedMultiLogImpl` to provide a function `inv`
//! that encodes any invariants `UntrustedMultiLogImpl` wants maintained
//! across invocations of its functions. This implementation will then
//! guarantee that `inv` holds on any call to an `UntrustedMultiLogImpl`
//! method, and demand that the method preserve that invariant.

use std::fmt::Write;

use crate::multilog::multilogimpl_v::UntrustedMultiLogImpl;
use crate::multilog::multilogspec_t::AbstractMultiLogState;
use crate::pmem::pmemspec_t::*;
use crate::pmem::wrpm_t::*;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use deps_hack::rand::Rng;

verus! {

    // This is the specification that `MultiLogImpl` provides for data
    // bytes it reads. It says that those bytes are correct unless
    // there was corruption on the persistent memory between the last
    // write and this read.
    pub open spec fn read_correct_modulo_corruption(bytes: Seq<u8>, true_bytes: Seq<u8>,
                                                    impervious_to_corruption: bool) -> bool
    {
        if impervious_to_corruption {
            // If the region is impervious to corruption, the bytes read
            // must match the true bytes, i.e., the bytes last written.

            bytes == true_bytes
        }
        else {
            // Otherwise, there must exist a sequence of distinct
            // addresses `addrs` such that the nth byte of `bytes` is
            // a possibly corrupted version of the nth byte of
            // `true_bytes` read from the nth address in `addrs`.  We
            // don't require the sequence of addresses to be
            // contiguous because the data might not be contiguous on
            // disk (e.g., if it wrapped around the log area).

            exists |addrs: Seq<int>| {
                &&& all_elements_unique(addrs)
                &&& #[trigger] maybe_corrupted(bytes, true_bytes, addrs)
            }
        }
    }

    // This specification function indicates whether a given view of
    // memory can only crash in a way that, after recovery, leads to a
    // certain abstract state.
    pub open spec fn can_only_crash_as_state(
        pm_regions_view: PersistentMemoryRegionsView,
        multilog_id: u128,
        state: AbstractMultiLogState,
    ) -> bool
    {
        forall |s| #[trigger] pm_regions_view.can_crash_as(s) ==>
            UntrustedMultiLogImpl::recover(s, multilog_id) == Some(state)
    }

    // A `TrustedMultiLogPermission` is the type of a tracked object
    // indicating permission to update memory. It restricts updates so
    // that if a crash happens, the resulting memory `mem` satisfies
    // `is_state_allowable(mem)`.
    //
    // The struct is defined in this file, and it has a non-public
    // field, so the only code that can create one is in this file.
    // So untrusted code in other files can't create one, and we can
    // rely on it to restrict access to persistent memory.
    #[allow(dead_code)]
    pub struct TrustedMultiLogPermission {
        ghost is_state_allowable: spec_fn(Seq<Seq<u8>>) -> bool
    }

    impl CheckPermission<Seq<Seq<u8>>> for TrustedMultiLogPermission {
        closed spec fn check_permission(&self, state: Seq<Seq<u8>>) -> bool {
            (self.is_state_allowable)(state)
        }
    }

    impl TrustedMultiLogPermission {

        // This is one of two constructors for `TrustedMultiLogPermission`.
        // It conveys permission to do any update as long as a
        // subsequent crash and recovery can only lead to given
        // abstract state `state`.
        proof fn new_one_possibility(multilog_id: u128, state: AbstractMultiLogState) -> (tracked perm: Self)
            ensures
                forall |s| #[trigger] perm.check_permission(s) <==>
                    UntrustedMultiLogImpl::recover(s, multilog_id) == Some(state)
        {
            Self {
                is_state_allowable: |s| UntrustedMultiLogImpl::recover(s, multilog_id) == Some(state)
            }
        }

        // This is the second of two constructors for
        // `TrustedMultiLogPermission`.  It conveys permission to do any
        // update as long as a subsequent crash and recovery can only
        // lead to one of two given abstract states `state1` and
        // `state2`.
        proof fn new_two_possibilities(
            multilog_id: u128,
            state1: AbstractMultiLogState,
            state2: AbstractMultiLogState
        ) -> (tracked perm: Self)
            ensures
                forall |s| #[trigger] perm.check_permission(s) <==> {
                    ||| UntrustedMultiLogImpl::recover(s, multilog_id) == Some(state1)
                    ||| UntrustedMultiLogImpl::recover(s, multilog_id) == Some(state2)
                }
        {
            Self {
                is_state_allowable: |s| {
                    ||| UntrustedMultiLogImpl::recover(s, multilog_id) == Some(state1)
                    ||| UntrustedMultiLogImpl::recover(s, multilog_id) == Some(state2)
                }
            }
        }
    }

    // This enumeration represents the various errors that can be
    // returned from multilog operations. They're self-explanatory.
    #[derive(Debug)]
    pub enum MultiLogErr {
        CantSetupWithFewerThanOneRegion { },
        CantSetupWithMoreThanU32MaxRegions { },
        InsufficientSpaceForSetup { which_log: u32, required_space: u64 },
        StartFailedDueToMultilogIDMismatch { which_log: u32, multilog_id_expected: u128, multilog_id_read: u128 },
        StartFailedDueToRegionSizeMismatch { which_log: u32, region_size_expected: u64, region_size_read: u64 },
        StartFailedDueToProgramVersionNumberUnsupported { which_log: u32, version_number: u64, max_supported: u64 },
        StartFailedDueToInvalidMemoryContents { which_log: u32 },
        CRCMismatch,
        InvalidLogIndex { },
        InsufficientSpaceForAppend { available_space: u64 },
        CantReadBeforeHead { head: u128 },
        CantReadPastTail { tail: u128 },
        CantAdvanceHeadPositionBeforeHead { head: u128 },
        CantAdvanceHeadPositionBeyondTail { tail: u128 },
        PmemErr { err: PmemError }
    }

    // This executable method can be called to compute a random GUID.
    // It uses the external `rand` crate.
    #[verifier::external_body]
    pub exec fn generate_fresh_multilog_id() -> (out: u128)
    {
        deps_hack::rand::thread_rng().gen::<u128>()
    }

    /// A `MultiLogImpl` wraps one `UntrustedMultiLogImpl` and a
    /// collection of persistent memory regions to provide the
    /// executable interface that turns the persistent memory regions
    /// into a set of logs in which any subset of logs can be updated
    /// atomically.
    ///
    /// The `untrusted_log_impl` field is the wrapped
    /// `UntrustedMultiLogImpl`.
    ///
    /// The `multilog_id` field is the multilog ID. It's ghost.
    ///
    /// The `wrpm_regions` field contains the write-restricted persistent
    /// memory. This memory will only allow updates allowed by a
    /// tracked `TrustedMultiLogPermission`. So we can pass `wrpm_regions` to an
    /// untrusted method, along with a restricting
    /// `TrustedMultiLogPermission`, to limit what it's allowed to do.

    pub struct MultiLogImpl<PMRegions: PersistentMemoryRegions> {
        untrusted_log_impl: UntrustedMultiLogImpl,
        multilog_id: Ghost<u128>,
        wrpm_regions: WriteRestrictedPersistentMemoryRegions<TrustedMultiLogPermission, PMRegions>
    }

    impl <PMRegions: PersistentMemoryRegions> MultiLogImpl<PMRegions> {
        // The view of a `MultiLogImpl` is whatever the
        // `UntrustedMultiLogImpl` it wraps says it is.
        pub closed spec fn view(self) -> AbstractMultiLogState
        {
            self.untrusted_log_impl@
        }

        // The constants of a `MultiLogImpl` are whatever the
        // persistent memory it wraps says they are.
        pub closed spec fn constants(&self) -> PersistentMemoryConstants {
            self.wrpm_regions.constants()
        }

        // This is the validity condition that is maintained between
        // calls to methods on `self`.
        //
        // That is, each of the trusted wrappers on untrusted methods
        // below (e.g., `commit`, `advance_head`) can count on `valid`
        // holding because it demands that each untrusted method
        // maintains it.
        //
        // One element of `valid` is that the untrusted `inv` function
        // holds.
        //
        // The other element of `valid` is that the persistent memory,
        // if it crashes and recovers, must represent the current
        // abstract state with pending tentative appends dropped.
        pub closed spec fn valid(self) -> bool {
            &&& self.untrusted_log_impl.inv(&self.wrpm_regions, self.multilog_id@)
            &&& can_only_crash_as_state(self.wrpm_regions@, self.multilog_id@, self@.drop_pending_appends())
        }

        proof fn lemma_valid_implies_wrpm_inv(self)
            requires
                self.valid()
            ensures
                self.wrpm_regions.inv()
        {
            self.untrusted_log_impl.lemma_inv_implies_wrpm_inv(&self.wrpm_regions, self.multilog_id@);
        }

        proof fn lemma_untrusted_log_inv_implies_valid(self)
            requires
                self.untrusted_log_impl.inv(&self.wrpm_regions, self.multilog_id@)
            ensures
                self.valid()
        {
            self.untrusted_log_impl.lemma_inv_implies_can_only_crash_as(&self.wrpm_regions, self.multilog_id@);
        }

        // The `setup` method sets up persistent memory regions `pm_regions`
        // to store an initial empty multilog. It returns a vector
        // listing the capacities of the logs as well as a fresh
        // multilog ID to uniquely identify it. See `README.md` for more
        // documentation.
        pub exec fn setup(pm_regions: &mut PMRegions) -> (result: Result<(Vec<u64>, u128), MultiLogErr>)
            requires
                old(pm_regions).inv(),
            ensures
                pm_regions.inv(),
                pm_regions@.no_outstanding_writes(),
                match result {
                    Ok((log_capacities, multilog_id)) => {
                        let state = AbstractMultiLogState::initialize(log_capacities@);
                        &&& pm_regions@.len() == old(pm_regions)@.len()
                        &&& pm_regions@.len() >= 1
                        &&& pm_regions@.len() <= u32::MAX
                        &&& log_capacities@.len() == pm_regions@.len()
                        &&& forall |i: int| 0 <= i < pm_regions@.len() ==>
                               #[trigger] log_capacities@[i] <= pm_regions@[i].len()
                        &&& forall |i: int| 0 <= i < pm_regions@.len() ==>
                               #[trigger] pm_regions@[i].len() == old(pm_regions)@[i].len()
                        &&& can_only_crash_as_state(pm_regions@, multilog_id, state)
                        &&& UntrustedMultiLogImpl::recover(pm_regions@.committed(), multilog_id) == Some(state)
                        // Required by the `start` function's precondition. Putting this in the
                        // postcond of `setup` ensures that the trusted caller doesn't have to prove it
                        &&& UntrustedMultiLogImpl::recover(pm_regions@.flush().committed(), multilog_id) == Some(state)
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
            let multilog_id = generate_fresh_multilog_id();
            let capacities = UntrustedMultiLogImpl::setup(pm_regions, multilog_id)?;
            Ok((capacities, multilog_id))
        }

        // The `start` method creates an `UntrustedMultiLogImpl` out
        // of a set of persistent memory regions. It's assumed that
        // those regions were initialized with `setup` and then only
        // multilog operations were allowed to mutate them. See
        // `README.md` for more documentation and an example of use.
        pub exec fn start(pm_regions: PMRegions, multilog_id: u128)
                          -> (result: Result<MultiLogImpl<PMRegions>, MultiLogErr>)
            requires
                pm_regions.inv(),
                UntrustedMultiLogImpl::recover(pm_regions@.flush().committed(), multilog_id).is_Some(),
            ensures
                match result {
                    Ok(trusted_log_impl) => {
                        &&& trusted_log_impl.valid()
                        &&& trusted_log_impl.constants() == pm_regions.constants()
                        &&& Some(trusted_log_impl@) == UntrustedMultiLogImpl::recover(pm_regions@.flush().committed(),
                                                                                     multilog_id)
                    },
                    Err(MultiLogErr::CRCMismatch) => !pm_regions.constants().impervious_to_corruption,
                    Err(MultiLogErr::InsufficientSpaceForSetup { which_log, required_space }) => {
                        let flushed_regions = pm_regions@.flush();
                        &&& 0 <= which_log < flushed_regions.len()
                        &&& pm_regions@[which_log as int].len() < required_space
                    },
                    _ => false
                }
        {
            // We allow the untrusted `start` method to update memory
            // as part of its initialization. But, to avoid bugs
            // stemming from crashes in the middle of this routine, we
            // must restrict how it updates memory. We must only let
            // it write such that, if a crash happens in the middle,
            // it doesn't change the persistent state.

            let ghost state = UntrustedMultiLogImpl::recover(pm_regions@.flush().committed(), multilog_id).get_Some_0();
            let mut wrpm_regions = WriteRestrictedPersistentMemoryRegions::new(pm_regions);
            let tracked perm = TrustedMultiLogPermission::new_one_possibility(multilog_id, state);
            let untrusted_log_impl =
                UntrustedMultiLogImpl::start(&mut wrpm_regions, multilog_id, Tracked(&perm), Ghost(state))?;
            Ok(
                MultiLogImpl {
                    untrusted_log_impl,
                    multilog_id:  Ghost(multilog_id),
                    wrpm_regions
                },
            )
        }

        // The `tentatively_append` method tentatively appends
        // `bytes_to_append` to the end of log number `which_log` in
        // the multilog. It's tentative in that crashes will undo the
        // appends, and reads aren't allowed in the tentative part of
        // the log. See `README.md` for more documentation and examples
        // of use.
        pub exec fn tentatively_append(&mut self, which_log: u32, bytes_to_append: &[u8])
                                       -> (result: Result<u128, MultiLogErr>)
            requires
                old(self).valid(),
            ensures
                self.valid(),
                self.constants() == old(self).constants(),
                match result {
                    Ok(offset) => {
                        let state = old(self)@[which_log as int];
                        &&& which_log < old(self)@.num_logs()
                        &&& offset == state.head + state.log.len() + state.pending.len()
                        &&& self@ == old(self)@.tentatively_append(which_log as int, bytes_to_append@)
                    },
                    Err(MultiLogErr::InvalidLogIndex { }) => {
                        &&& which_log >= self@.num_logs()
                        &&& self@ == old(self)@
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
            // For crash safety, we must restrict the untrusted code's
            // writes to persistent memory. We must only let it write
            // such that, if a crash happens in the middle of a write,
            // the view of the persistent state is the current
            // state with pending appends dropped.
            let tracked perm = TrustedMultiLogPermission::new_one_possibility(self.multilog_id@, self@.drop_pending_appends());
            self.untrusted_log_impl.tentatively_append(&mut self.wrpm_regions, which_log, bytes_to_append,
                                                       self.multilog_id, Tracked(&perm))
        }

        // The `commit` method atomically commits all tentative
        // appends that have been done to `self` since the last
        // commit. The commit is atomic in that even if there's a
        // crash in the middle, the recovered-to state either reflects
        // all those tentative appends or none of them. See `README.md`
        // for more documentation and examples of use.
        pub exec fn commit(&mut self) -> (result: Result<(), MultiLogErr>)
            requires
                old(self).valid(),
            ensures
                self.valid(),
                self.constants() == old(self).constants(),
                match result {
                    Ok(()) => self@ == old(self)@.commit(),
                    _ => false,
                }
        {
            // For crash safety, we must restrict the untrusted code's
            // writes to persistent memory. We must only let it write
            // such that, if a crash happens in the middle of a write,
            // the view of the persistent state is either the current
            // state with all pending appends dropped or the current
            // state with all uncommitted appends committed.
            let tracked perm = TrustedMultiLogPermission::new_two_possibilities(self.multilog_id@, self@.drop_pending_appends(),
                                                                        self@.commit().drop_pending_appends());
            self.untrusted_log_impl.commit(&mut self.wrpm_regions, self.multilog_id, Tracked(&perm))
        }

        // The `advance_head` method advances the head of log number
        // `which_log` to virtual new head position `new_head`. It
        // doesn't do this tentatively; it completes it durably before
        // returning. However, `advance_head` doesn't commit tentative
        // appends; to do that, you need a separate call to
        // `commit`. See `README.md` for more documentation and examples
        // of use.
        pub exec fn advance_head(&mut self, which_log: u32, new_head: u128) -> (result: Result<(), MultiLogErr>)
            requires
                old(self).valid(),
            ensures
                self.valid(),
                self.constants() == old(self).constants(),
                match result {
                    Ok(()) => {
                        let w = which_log as int;
                        &&& which_log < self@.num_logs()
                        &&& old(self)@[w].head <= new_head <= old(self)@[w].head + old(self)@[w].log.len()
                        &&& self@ == old(self)@.advance_head(w, new_head as int)
                    },
                    Err(MultiLogErr::InvalidLogIndex{ }) => {
                        &&& which_log >= self@.num_logs()
                        &&& self@ == old(self)@
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
                    _ => false,
                }
        {
            // For crash safety, we must restrict the untrusted code's
            // writes to persistent memory. We must only let it write
            // such that, if a crash happens in the middle of a write,
            // the view of the persistent state is either the current
            // state or the current state with the head advanced.
            let tracked perm = TrustedMultiLogPermission::new_two_possibilities(
                self.multilog_id@,
                self@.drop_pending_appends(),
                self@.advance_head(which_log as int, new_head as int).drop_pending_appends()
            );
            self.untrusted_log_impl.advance_head(&mut self.wrpm_regions, which_log, new_head,
                                                 self.multilog_id, Tracked(&perm))
        }

        // The `read` method reads `len` bytes from log number
        // `which_log` starting at virtual position `pos`. It isn't
        // allowed to read earlier than the head or past the committed
        // tail. See `README.md` for more documentation and examples of
        // use.
        pub exec fn read(&self, which_log: u32, pos: u128, len: u64) -> (result: Result<Vec<u8>, MultiLogErr>)
            requires
                self.valid(),
                pos + len <= u128::MAX,
            ensures
                ({
                    let state = self@[which_log as int];
                    let head = state.head;
                    let log = state.log;
                    match result {
                        Ok(bytes) => {
                            let true_bytes = self@.read(which_log as int, pos as int, len as int);
                            &&& which_log < self@.num_logs()
                            &&& pos >= head
                            &&& pos + len <= head + log.len()
                            &&& read_correct_modulo_corruption(bytes@, true_bytes,
                                                             self.constants().impervious_to_corruption)
                        },
                        Err(MultiLogErr::InvalidLogIndex { }) => {
                            which_log >= self@.num_logs()
                        },
                        Err(MultiLogErr::CantReadBeforeHead{ head: head_pos }) => {
                            &&& which_log < self@.num_logs()
                            &&& pos < head
                            &&& head_pos == head
                        },
                        Err(MultiLogErr::CantReadPastTail{ tail }) => {
                            &&& which_log < self@.num_logs()
                            &&& pos + len > tail
                            &&& tail == head + log.len()
                        },
                        _ => false
                    }
                })
        {
            self.untrusted_log_impl.read(&self.wrpm_regions, which_log, pos, len, self.multilog_id)
        }

        // The `get_head_tail_and_capacity` method returns three
        // pieces of metadata about log number `which_log`: the
        // virtual head position, the virtual tail position, and the
        // capacity. The capacity is the maximum number of bytes there
        // can be in the log past the head, including bytes in
        // tentative appends that haven't been committed yet. See
        // `README.md` for more documentation and examples of use.
        pub exec fn get_head_tail_and_capacity(&self, which_log: u32) -> (result: Result<(u128, u128, u64), MultiLogErr>)
            requires
                self.valid()
            ensures
                match result {
                    Ok((result_head, result_tail, result_capacity)) => {
                        let inf_log = self@[which_log as int];
                        &&& which_log < self@.num_logs()
                        &&& result_head == inf_log.head
                        &&& result_tail == inf_log.head + inf_log.log.len()
                        &&& result_capacity == inf_log.capacity
                    },
                    Err(MultiLogErr::InvalidLogIndex{ }) => {
                        which_log >= self@.num_logs()
                    },
                    _ => false
                }
        {
            self.untrusted_log_impl.get_head_tail_and_capacity(&self.wrpm_regions, which_log, self.multilog_id)
        }
    }

}
