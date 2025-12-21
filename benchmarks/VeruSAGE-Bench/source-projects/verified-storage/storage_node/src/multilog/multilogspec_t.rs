//! This file contains the trusted specification for an abstract
//! multilog, which has type `AbstractMultiLogState`.
//!
//! Although the verifier is run on this file, it needs to be
//! carefully read and audited to be confident of the correctness of
//! this specification for the multilog implementation.
//!
//! An `AbstractMultiLogState` has the following operations:
//!
//! `initialize(capacities: Seq<u64>) -> AbstractMultiLogState`
//!
//! This static function creates an initial multilog with the given
//! capacities.
//!
//! `num_logs(self) -> nat`
//!
//! This method returns the number of logs in the multilog.
//!
//! `tentatively_append(self, which_log: int, bytes_to_append: Seq<u8>) -> Self`
//!
//! This method tentatively appends the given bytes to the end of the
//! log in the multilog with the given index.
//!
//! `commit(self) -> Self`
//!
//! This method commits all tentative appends atomically across all
//! logs in the multilog.
//!
//! `read(self, which_log: int, pos: int, len: int) -> Seq<u8>`
//!
//! This method reads a certain number of bytes from one of the logs
//! at a certain logical position.
//!
//! `drop_pending_appends(self) -> Self`
//!
//! This method drops all pending appends. It's not meant to be
//! explicitly invoked by clients; it's a model of what clients should
//! consider to have happened during a crash.

use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

verus! {
    
    // An `AbstractLogState` is an abstraction of a single log, of
    // which an abstract multilog is composed. Its fields are:
    //
    // `head` -- the logical position of the first accessible byte
    // in the log
    //
    // `log` -- the accessible bytes in the log, logically starting
    // at position `head`
    //
    // `pending` -- the bytes tentatively appended past the end of the
    // log, which will not become part of the log unless committed
    // and which will be discarded on a crash
    //
    // `capacity` -- the maximum length of the `log` field
    #[verifier::ext_equal]
    pub struct AbstractLogState {
        pub head: int,
        pub log: Seq<u8>,
        pub pending: Seq<u8>,
        pub capacity: int,
    }

    impl AbstractLogState {

        // This is the specification for the initial state of an
        // abstract log.
        pub open spec fn initialize(capacity: int) -> Self {
            Self {
                head: 0int,
                log: Seq::<u8>::empty(),
                pending: Seq::<u8>::empty(),
                capacity: capacity
            }
        }

        // This is the specification for what it means to tentatively
        // append to a log. It appends the given bytes to the
        // `pending` field.
        pub open spec fn tentatively_append(self, bytes: Seq<u8>) -> Self {
            Self { pending: self.pending + bytes, ..self }
        }

        // This is the specification for what it means to commit a
        // log.  It adds all pending bytes to the log and clears the
        // pending bytes.
        pub open spec fn commit(self) -> Self {
            Self { log: self.log + self.pending, pending: Seq::<u8>::empty(), ..self }
        }

        // This is the specification for what it means to advance the
        // head to a given new value `new_value`.
        pub open spec fn advance_head(self, new_head: int) -> Self
        {
            let new_log = self.log.subrange(new_head - self.head, self.log.len() as int);
            Self { head: new_head, log: new_log, ..self }
        }

        // This is the specification for what it means to read `len`
        // bytes from a certain virtual position `pos` in the abstract
        // log.
        pub open spec fn read(self, pos: int, len: int) -> Seq<u8>
        {
            self.log.subrange(pos - self.head, pos - self.head + len)
        }

        // This is the specification for what it means to drop pending
        // appends. (This isn't a user-invokable operation; it's what
        // happens on a crash.)
        pub open spec fn drop_pending_appends(self) -> Self
        {
            Self { pending: Seq::<u8>::empty(), ..self }
        }
    }
    
    // An `AbstractMultiLogState` is an abstraction of a collection of
    // logs that can be atomically collectively appended to. It
    // consists of a sequence of logs of type `AbstractLogState`.
    #[verifier::ext_equal]
    pub struct AbstractMultiLogState {
        pub states: Seq<AbstractLogState>
    }

    #[verifier::ext_equal]
    impl AbstractMultiLogState {

        // This is the specification for the number of logs in a
        // multilog.
        pub open spec fn num_logs(self) -> nat {
            self.states.len()
        }

        // This is the specification for indexing into the sequence of
        // logs and getting the one at the given index `which_log`. Naming
        // it `spec_index` means it will be used whenever a term `s[w]` is
        // used in a specification where `s` is an `AbstractMultiLogState`.
        pub open spec fn spec_index(self, which_log: int) -> AbstractLogState {
            self.states[which_log]
        }

        // This is the specification for the initial state of an
        // abstract multilog.
        pub open spec fn initialize(capacities: Seq<u64>) -> Self {
            Self {
                states: Seq::<AbstractLogState>::new(capacities.len(),
                    |i| AbstractLogState::initialize(capacities[i] as int))
            }
        }

        // This is the specification for the operation of tentatively
        // appending to an abstract multilog.
        pub open spec fn tentatively_append(self, which_log: int, bytes_to_append: Seq<u8>) -> Self {
            Self {
                states: self.states.update(which_log, self.states[which_log].tentatively_append(bytes_to_append))
            }
        }

        // This is the specification for the operation of committing
        // all pending appends to an abstract multilog. It atomically
        // commits all such pending appends at once.
        pub open spec fn commit(self) -> Self {
            Self {
                states: self.states.map(|_idx, s: AbstractLogState| s.commit())
            }
        }

        // This is the specification for the operation of advancing
        // the head of one of the logs in a multilog.
        pub open spec fn advance_head(self, which_log: int, new_head: int) -> Self {
            Self {
                states: self.states.update(which_log, self.states[which_log].advance_head(new_head))
            }
        }

        // This is the specification for what it means to read `len`
        // bytes from a certain virtual position `pos` in the log
        // with a certain index `which_log`:
        pub open spec fn read(self, which_log: int, pos: int, len: int) -> Seq<u8>
        {
            self.states[which_log].read(pos, len)
        }

        // This is the specification for the operation of dropping all
        // pending appends to a multilog.
        pub open spec fn drop_pending_appends(self) -> Self {
            Self {
                states: self.states.map(|_idx, s: AbstractLogState| s.drop_pending_appends())
            }
        }
    }

}
