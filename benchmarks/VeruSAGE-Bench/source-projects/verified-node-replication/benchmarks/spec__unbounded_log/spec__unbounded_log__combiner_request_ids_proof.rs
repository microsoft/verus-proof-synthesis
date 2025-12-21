use vstd::prelude::*;

fn main() {}
pub type ReqId=nat;
pub type NodeId=nat;
pub type LogIdx=nat;

verus!{

// File: spec/unbounded_log.rs
#[is_variant]
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

impl CombinerState {

    pub open spec fn queued_ops(self) -> Seq<ReqId> {
        match self {
            CombinerState::Ready => Seq::empty(),
            CombinerState::Placed { queued_ops } => queued_ops,
            CombinerState::LoadedLocalVersion { queued_ops, .. } => queued_ops,
            CombinerState::Loop { queued_ops, .. } => queued_ops,
            CombinerState::UpdatedVersion { queued_ops, .. } => queued_ops,
        }
    }

}


pub proof fn combiner_request_ids_proof(combiners: Map<NodeId, CombinerState>) -> Set<ReqId>
    requires
        combiners.dom().finite(),
    decreases combiners.dom().len(),
{
    if combiners.dom().len() == 0 {
        Set::empty()
    } else {
        let node_id = combiners.dom().choose();
        let s1 = combiner_request_ids_proof(combiners.remove(node_id));
        s1 + seq_to_set(
            combiners[node_id].queued_ops(),
        )
        // combiner_request_ids_proof(combiners.remove(node_id)) + seq_to_set(combiners[node_id].queued_ops())

    }
}


// File: spec/utils.rs
pub open spec fn seq_to_set<A>(seq: Seq<A>) -> Set<A> {
    Set::new(|a: A| seq.contains(a))
}

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
}
}
