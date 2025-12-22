use vstd::prelude::*;

fn main() {}
pub type ReqId=nat;
pub type NodeId=nat;
pub type LogIdx=nat;

verus!{

// File: spec/types.rs
pub tracked struct LogEntry<DT: Dispatch> {
    pub op: DT::WriteOperation,
    pub node_id: NodeId,
}


// File: spec/unbounded_log.rs
/*#[is_variant]
pub ghost enum ReadonlyState<DT: Dispatch> {
    /// a new read request that has come in
    Init { op: DT::ReadOperation },
    /// has read the version upper bound value
    VersionUpperBound { op: DT::ReadOperation, version_upper_bound: LogIdx },
    /// ready to read
    ReadyToRead { op: DT::ReadOperation, version_upper_bound: LogIdx, node_id: NodeId },
    /// read request is done
    Done { op: DT::ReadOperation, version_upper_bound: LogIdx, node_id: NodeId, ret: DT::Response },
}

#[is_variant]
pub ghost enum UpdateState<DT: Dispatch> {
    /// upated request has entered the system
    Init { op: DT::WriteOperation },
    /// update has been placed into the log
    Placed { op: DT::WriteOperation, idx: LogIdx },
    /// the update has been applied to the data structure
    Applied { ret: DT::Response, idx: LogIdx },
    /// the update is ready to be returned
    Done { ret: DT::Response, idx: LogIdx },
}

#[is_variant]
pub ghost enum CombinerState {
    Ready,
    Placed { queued_ops: Seq<ReqId> },
    LoadedLocalVersion { queued_ops: Seq<ReqId>, lversion: LogIdx },
    Loop {
        /// sequence of request ids of the local node
        queued_ops: Seq<ReqId>,
        /// version of the local replica
        lversion: LogIdx,
        /// index into the queued ops
        idx: nat,
        /// the global tail we'v read
        tail: LogIdx,
    },
    UpdatedVersion { queued_ops: Seq<ReqId>, tail: LogIdx },
}
*/
pub open spec fn compute_nrstate_at_version<DT: Dispatch>(
    log: Map<LogIdx, LogEntry<DT>>,
    version: LogIdx,
) -> DT::View
    recommends
        forall|i| 0 <= i < version ==> log.contains_key(i),
    decreases version,
{
    if version == 0 {
        DT::init_spec()
    } else {
        let ver = (version - 1) as nat;
        DT::dispatch_mut_spec(compute_nrstate_at_version(log, ver), log[ver].op).0
    }
}

pub proof fn compute_nrstate_at_version_preserves<DT: Dispatch>(
    a: Map<LogIdx, LogEntry<DT>>,
    b: Map<LogIdx, LogEntry<DT>>,
    version: LogIdx,
)
    requires
        forall|i| 0 <= i < version ==> a.contains_key(i),
        forall|i| 0 <= i < version ==> a[i] == b[i],
    ensures
        compute_nrstate_at_version(a, version) == compute_nrstate_at_version(b, version),
    decreases version,
{
    if version > 0 {
        compute_nrstate_at_version_preserves(a, b, (version - 1) as nat);
    }
}


// File: lib.rs
#[verus::trusted]
pub trait Dispatch: Sized {
    /// Type of a read-only operation. Operations of this type do not mutate the data structure.
    type ReadOperation: Sized;

    /// Type of a write operation. Operations of this type may mutate the data structure.
    /// Write operations are sent between replicas.
    type WriteOperation: Sized + Send;

    /// Type of the response of either a read or write operation.
    type Response: Sized;

    /// Type of the view of the data structure for specs and proofs.
    type View;

    spec fn init_spec() -> Self::View;

    spec fn dispatch_mut_spec(ds: Self::View, op: Self::WriteOperation) -> (
        Self::View,
        Self::Response,
    );


}
}
