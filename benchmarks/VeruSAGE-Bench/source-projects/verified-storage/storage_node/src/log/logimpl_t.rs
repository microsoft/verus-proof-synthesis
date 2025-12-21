//! This file contains the trusted implementation of a `LogImpl`.
//! Although the verifier is run on this file, it needs to be
//! carefully read and audited to be confident of the correctness of
//! this log implementation.
//!
//! Fortunately, it delegates most of its work to an untrusted struct
//! `UntrustedLogImpl`, which doesn't need to be read or audited. It
//! forces the `UntrustedLogImpl` to satisfy certain postconditions,
//! and also places restrictions on what `UntrustedLogImpl` can do to
//! persistent memory. These restrictions ensure that even if the
//! system or process crashes in the middle of an operation, the
//! system will still recover to a consistent state.
//!
//! It requires `UntrustedLogImpl` to implement routines that do the
//! various log operations like read and commit.
//!
//! It also requires `UntrustedLogImpl` to provide a function
//! `UntrustedLogImpl::recover`, which specifies what its `start`
//! routine will do to recover after a crash. It requires its `start`
//! routine to satisfy that specification. It also uses it to limit
//! how `UntrustedLogImpl` writes to memory: It can only perform
//! updates that, if incompletely performed before a crash, still
//! leave the system in a valid state. The `recover` function takes a
//! second parameter, the `log_id` which is passed to the start
//! routine.
//!
//! It also requires `UntrustedLogImpl` to provide a function `view`
//! that converts the current state into an abstract log. It requires
//! that performing a certain operation on the `UntrustedLogImpl`
//! causes a corresponding update to its abstract view. For instance,
//! calling the `u.commit()` method should cause the resulting
//! `u.view()` to become `old(u).view().commit()`.
//!
//! It also permits `UntrustedLogImpl` to provide a function `inv`
//! that encodes any invariants `UntrustedLogImpl` wants maintained
//! across invocations of its functions. This implementation will then
//! guarantee that `inv` holds on any call to an `UntrustedLogImpl`
//! method, and demand that the method preserve that invariant.

use std::fmt::Write;

use crate::log::logimpl_v::UntrustedLogImpl;
use crate::log::logspec_t::AbstractLogState;
use crate::pmem::pmemspec_t::*;
use crate::pmem::wrpm_t::*;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use deps_hack::rand::Rng;

verus! {

    // This is the specification that `LogImpl` provides for data
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
        pm_region_view: PersistentMemoryRegionView,
        log_id: u128,
        state: AbstractLogState,
    ) -> bool
    {
        forall |s| #[trigger] pm_region_view.can_crash_as(s) ==>
            UntrustedLogImpl::recover(s, log_id) == Some(state)
    }

    // A `TrustedPermission` is the type of a tracked object
    // indicating permission to update memory. It restricts updates so
    // that if a crash happens, the resulting memory `mem` satisfies
    // `is_state_allowable(mem)`.
    //
    // The struct is defined in this file, and it has a non-public
    // field, so the only code that can create one is in this file.
    // So untrusted code in other files can't create one, and we can
    // rely on it to restrict access to persistent memory.
    #[allow(dead_code)]
    pub struct TrustedPermission {
        ghost is_state_allowable: spec_fn(Seq<u8>) -> bool
    }

    impl CheckPermission<Seq<u8>> for TrustedPermission {
        closed spec fn check_permission(&self, state: Seq<u8>) -> bool {
            (self.is_state_allowable)(state)
        }
    }

    impl TrustedPermission {

        // This is one of two constructors for `TrustedPermission`.
        // It conveys permission to do any update as long as a
        // subsequent crash and recovery can only lead to given
        // abstract state `state`.
        proof fn new_one_possibility(log_id: u128, state: AbstractLogState) -> (tracked perm: Self)
            ensures
                forall |s| #[trigger] perm.check_permission(s) <==>
                    UntrustedLogImpl::recover(s, log_id) == Some(state)
        {
            Self {
                is_state_allowable: |s| UntrustedLogImpl::recover(s, log_id) == Some(state)
            }
        }

        // This is the second of two constructors for
        // `TrustedPermission`.  It conveys permission to do any
        // update as long as a subsequent crash and recovery can only
        // lead to one of two given abstract states `state1` and
        // `state2`.
        proof fn new_two_possibilities(
            log_id: u128,
            state1: AbstractLogState,
            state2: AbstractLogState
        ) -> (tracked perm: Self)
            ensures
                forall |s| #[trigger] perm.check_permission(s) <==> {
                    ||| UntrustedLogImpl::recover(s, log_id) == Some(state1)
                    ||| UntrustedLogImpl::recover(s, log_id) == Some(state2)
                }
        {
            Self {
                is_state_allowable: |s| {
                    ||| UntrustedLogImpl::recover(s, log_id) == Some(state1)
                    ||| UntrustedLogImpl::recover(s, log_id) == Some(state2)
                }
            }
        }
    }

    // This enumeration represents the various errors that can be
    // returned from log operations. They're self-explanatory.
    // TODO: make `PmemErr` and `LogErr` handling cleaner
    #[derive(Debug)]
    pub enum LogErr {
        InsufficientSpaceForSetup { required_space: u64 },
        StartFailedDueToLogIDMismatch { log_id_expected: u128, log_id_read: u128 },
        StartFailedDueToRegionSizeMismatch { region_size_expected: u64, region_size_read: u64 },
        StartFailedDueToProgramVersionNumberUnsupported { version_number: u64, max_supported: u64 },
        StartFailedDueToInvalidMemoryContents,
        CRCMismatch,
        InsufficientSpaceForAppend { available_space: u64 },
        CantReadBeforeHead { head: u128 },
        CantReadPastTail { tail: u128 },
        CantAdvanceHeadPositionBeforeHead { head: u128 },
        CantAdvanceHeadPositionBeyondTail { tail: u128 },
        PmemErr { err: PmemError } // janky workaround so that callers can handle PmemErrors as LogErrors
    }

    // This executable method can be called to compute a random GUID.
    // It uses the external `rand` crate.
    #[verifier::external_body]
    pub exec fn generate_fresh_log_id() -> (out: u128)
    {
        deps_hack::rand::thread_rng().gen::<u128>()
    }

    /// A `LogImpl` wraps one `UntrustedLogImpl` and one persistent
    /// memory region to provide the executable interface that turns
    /// the persistent memory region into a log.
    ///
    /// The `untrusted_log_impl` field is the wrapped
    /// `UntrustedLogImpl`.
    ///
    /// The `log_id` field is the log ID. It's ghost.
    ///
    /// The `wrpm_region` field contains the write-restricted persistent
    /// memory. This memory will only allow updates allowed by a
    /// tracked `TrustedPermission`. So we can pass `wrpm_region` to an
    /// untrusted method, along with a restricting
    /// `TrustedPermission`, to limit what it's allowed to do.

    pub struct LogImpl<PMRegion: PersistentMemoryRegion> {
        untrusted_log_impl: UntrustedLogImpl,
        log_id: Ghost<u128>,
        wrpm_region: WriteRestrictedPersistentMemoryRegion<TrustedPermission, PMRegion>
    }

    impl <PMRegion: PersistentMemoryRegion> LogImpl<PMRegion> {
        // The view of a `LogImpl` is whatever the
        // `UntrustedLogImpl` it wraps says it is.
        pub closed spec fn view(self) -> AbstractLogState
        {
            self.untrusted_log_impl@
        }

        // The constants of a `LogImpl` are whatever the
        // persistent memory it wraps says they are.
        pub closed spec fn constants(&self) -> PersistentMemoryConstants {
            self.wrpm_region.constants()
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
            &&& self.untrusted_log_impl.inv(&self.wrpm_region, self.log_id@)
            &&& can_only_crash_as_state(self.wrpm_region@, self.log_id@, self@.drop_pending_appends())
        }

        // The `setup` method sets up persistent memory regions
        // `pm_region` to store an initial empty log. It returns a
        // vector listing the capacity of the log as well as a
        // fresh log ID to uniquely identify it. See `README.md`
        // for more documentation.
        pub exec fn setup(pm_region: &mut PMRegion) -> (result: Result<(u64, u128), LogErr>)
            requires
                old(pm_region).inv(),
            ensures
                pm_region.inv(),
                pm_region@.no_outstanding_writes(),
                match result {
                    Ok((log_capacity, log_id)) => {
                        let state = AbstractLogState::initialize(log_capacity as int);
                        &&& log_capacity <= pm_region@.len()
                        &&& pm_region@.len() == old(pm_region)@.len()
                        &&& can_only_crash_as_state(pm_region@, log_id, state)
                        &&& UntrustedLogImpl::recover(pm_region@.committed(), log_id) == Some(state)
                        // Required by the `start` function's precondition. Putting this in the
                        // postcond of `setup` ensures that the trusted caller doesn't have to prove it
                        &&& UntrustedLogImpl::recover(pm_region@.flush().committed(), log_id) == Some(state)
                        &&& state == state.drop_pending_appends()
                    },
                    Err(LogErr::InsufficientSpaceForSetup { required_space }) => {
                        &&& pm_region@ == old(pm_region)@.flush()
                        &&& pm_region@.len() < required_space
                    },
                    _ => false
                }
        {
            let log_id = generate_fresh_log_id();
            let capacities = UntrustedLogImpl::setup(pm_region, log_id)?;
            Ok((capacities, log_id))
        }

        // The `start` method creates an `UntrustedLogImpl` out of a
        // persistent memory region. It's assumed that the region was
        // initialized with `setup` and then only log operations were
        // allowed to mutate them. See `README.md` for more
        // documentation and an example of use.
        pub exec fn start(pm_region: PMRegion, log_id: u128) -> (result: Result<LogImpl<PMRegion>, LogErr>)
            requires
                pm_region.inv(),
                UntrustedLogImpl::recover(pm_region@.flush().committed(), log_id).is_Some(),
            ensures
                match result {
                    Ok(trusted_log_impl) => {
                        &&& trusted_log_impl.valid()
                        &&& trusted_log_impl.constants() == pm_region.constants()
                        &&& Some(trusted_log_impl@) == UntrustedLogImpl::recover(pm_region@.flush().committed(),
                                                                               log_id)
                    },
                    Err(LogErr::CRCMismatch) => !pm_region.constants().impervious_to_corruption,
                    Err(e) => e == LogErr::PmemErr{ err: PmemError::AccessOutOfRange },
                }
        {
            // We allow the untrusted `start` method to update memory
            // as part of its initialization. But, to avoid bugs
            // stemming from crashes in the middle of this routine, we
            // must restrict how it updates memory. We must only let
            // it write such that, if a crash happens in the middle,
            // it doesn't change the persistent state.

            let ghost state = UntrustedLogImpl::recover(pm_region@.flush().committed(), log_id).get_Some_0();
            let mut wrpm_region = WriteRestrictedPersistentMemoryRegion::new(pm_region);
            let tracked perm = TrustedPermission::new_one_possibility(log_id, state);
            let untrusted_log_impl =
                UntrustedLogImpl::start(&mut wrpm_region, log_id, Tracked(&perm), Ghost(state))?;
            Ok(
                LogImpl {
                    untrusted_log_impl,
                    log_id:  Ghost(log_id),
                    wrpm_region
                },
            )
        }

        // The `tentatively_append` method tentatively appends
        // `bytes_to_append` to the end of the log. It's tentative in
        // that crashes will undo the appends, and reads aren't
        // allowed in the tentative part of the log. See `README.md` for
        // more documentation and examples of use.
        pub exec fn tentatively_append(&mut self, bytes_to_append: &[u8]) -> (result: Result<u128, LogErr>)
            requires
                old(self).valid(),
            ensures
                self.valid(),
                self.constants() == old(self).constants(),
                match result {
                    Ok(offset) => {
                        let state = old(self)@;
                        &&& offset == state.head + state.log.len() + state.pending.len()
                        &&& self@ == old(self)@.tentatively_append(bytes_to_append@)
                    },
                    Err(LogErr::InsufficientSpaceForAppend { available_space }) => {
                        &&& self@ == old(self)@
                        &&& available_space < bytes_to_append@.len()
                        &&& {
                               ||| available_space == self@.capacity - self@.log.len() - self@.pending.len()
                               ||| available_space == u128::MAX - self@.head - self@.log.len() - self@.pending.len()
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
            let tracked perm = TrustedPermission::new_one_possibility(self.log_id@, self@.drop_pending_appends());
            self.untrusted_log_impl.tentatively_append(&mut self.wrpm_region, bytes_to_append,
                                                       self.log_id, Tracked(&perm))
        }

        // The `commit` method atomically commits all tentative
        // appends that have been done to `self` since the last
        // commit. The commit is atomic in that even if there's a
        // crash in the middle, the recovered-to state either reflects
        // all those tentative appends or none of them. See `README.md`
        // for more documentation and examples of use.
        pub exec fn commit(&mut self) -> (result: Result<(), LogErr>)
            requires
                old(self).valid(),
            ensures
                self.valid(),
                self.constants() == old(self).constants(),
                match result {
                    Ok(()) => self@ == old(self)@.commit(),
                    _ => false
                }
        {
            // For crash safety, we must restrict the untrusted code's
            // writes to persistent memory. We must only let it write
            // such that, if a crash happens in the middle of a write,
            // the view of the persistent state is either the current
            // state with all pending appends dropped or the current
            // state with all uncommitted appends committed.
            let tracked perm = TrustedPermission::new_two_possibilities(self.log_id@, self@.drop_pending_appends(),
                                                                        self@.commit().drop_pending_appends());
            self.untrusted_log_impl.commit(&mut self.wrpm_region, self.log_id, Tracked(&perm))
        }

        // The `advance_head` method advances the head of the log to
        // virtual new head position `new_head`. It doesn't do this
        // tentatively; it completes it durably before returning.
        // However, `advance_head` doesn't commit tentative appends;
        // to do that, you need a separate call to `commit`. See
        // `README.md` for more documentation and examples of use.
        pub exec fn advance_head(&mut self, new_head: u128) -> (result: Result<(), LogErr>)
            requires
                old(self).valid(),
            ensures
                self.valid(),
                self.constants() == old(self).constants(),
                match result {
                    Ok(()) => {
                        let state = old(self)@;
                        &&& state.head <= new_head <= state.head + state.log.len()
                        &&& self@ == old(self)@.advance_head(new_head as int)
                    },
                    Err(LogErr::CantAdvanceHeadPositionBeforeHead { head }) => {
                        &&& self@ == old(self)@
                        &&& head == self@.head
                        &&& new_head < head
                    },
                    Err(LogErr::CantAdvanceHeadPositionBeyondTail { tail }) => {
                        &&& self@ == old(self)@
                        &&& tail == self@.head + self@.log.len()
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
            let tracked perm = TrustedPermission::new_two_possibilities(
                self.log_id@,
                self@.drop_pending_appends(),
                self@.advance_head(new_head as int).drop_pending_appends()
            );
            self.untrusted_log_impl.advance_head(&mut self.wrpm_region, new_head,
                                                 self.log_id, Tracked(&perm))
        }

        // The `read` method reads `len` bytes from the log starting
        // at virtual position `pos`. It isn't allowed to read earlier
        // than the head or past the committed tail. See `README.md` for
        // more documentation and examples of use.
        #[verifier::spinoff_prover]
        pub exec fn read(&self, pos: u128, len: u64) -> (result: Result<Vec<u8>, LogErr>)
            requires
                self.valid(),
                pos + len <= u128::MAX,
            ensures
                ({
                    let state = self@;
                    let head = state.head;
                    let log = state.log;
                    match result {
                        Ok(bytes) => {
                            let true_bytes = self@.read(pos as int, len as int);
                            &&& pos >= head
                            &&& pos + len <= head + log.len()
                            &&& read_correct_modulo_corruption(bytes@, true_bytes,
                                                             self.constants().impervious_to_corruption)
                        },
                        Err(LogErr::CantReadBeforeHead{ head: head_pos }) => {
                            &&& pos < head
                            &&& head_pos == head
                        },
                        Err(LogErr::CantReadPastTail{ tail }) => {
                            &&& pos + len > tail
                            &&& tail == head + log.len()
                        },
                        Err(e) => e == LogErr::PmemErr{ err: PmemError::AccessOutOfRange },
                    }
                })
        {
            let (bytes, addrs) = self.untrusted_log_impl.read(&self.wrpm_region, pos, len, self.log_id)?;
            Ok(bytes)
        }

        // The `get_head_tail_and_capacity` method returns three
        // pieces of metadata about the log: the virtual head
        // position, the virtual tail position, and the capacity. The
        // capacity is the maximum number of bytes there can be in the
        // log past the head, including bytes in tentative appends
        // that haven't been committed yet. See `README.md` for more
        // documentation and examples of use.
        pub exec fn get_head_tail_and_capacity(&self) -> (result: Result<(u128, u128, u64), LogErr>)
            requires
                self.valid()
            ensures
                match result {
                    Ok((result_head, result_tail, result_capacity)) => {
                        &&& result_head == self@.head
                        &&& result_tail == self@.head + self@.log.len()
                        &&& result_capacity == self@.capacity
                    },
                    _ => false
                }
        {
            self.untrusted_log_impl.get_head_tail_and_capacity(&self.wrpm_region, self.log_id)
        }
    }

}
