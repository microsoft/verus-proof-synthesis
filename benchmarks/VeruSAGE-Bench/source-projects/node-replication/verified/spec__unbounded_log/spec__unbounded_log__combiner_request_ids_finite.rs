use vstd::prelude::*;

fn main() {}
pub type ReqId=nat;
pub type NodeId=nat;
pub type LogIdx=nat;

verus!{

// File: spec/unbounded_log.rs
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

#[via_fn]
proof fn combiner_request_ids_decreases(combiners: Map<NodeId, CombinerState>) {
    if combiners.dom().finite() {
        if combiners.dom().len() == 0 {
        } else {
            let node_id = combiners.dom().choose();
            assert(combiners.remove(node_id).dom().len() < combiners.dom().len());  // INCOMPLETENESS weird incompleteness
        }
    } else {
    }
}
pub open spec fn combiner_request_ids(combiners: Map<NodeId, CombinerState>) -> Set<ReqId>
    decreases combiners.dom().len(),
    when (combiners.dom().finite() && combiners.dom().len() >= 0)
    via combiner_request_ids_decreases
{
    if combiners.dom().finite() {
        if combiners.dom().len() == 0 {
            Set::empty()
        } else {
            let node_id = combiners.dom().choose();
            let req_ids = combiner_request_ids(combiners.remove(node_id));
            req_ids + seq_to_set(combiners[node_id].queued_ops())
        }
    } else {
        arbitrary()
    }
}

pub proof fn combiner_request_ids_finite(combiners: Map<NodeId, CombinerState>)
    requires
        combiners.dom().finite(),
    ensures
        combiner_request_ids(combiners).finite(),
    decreases combiners.dom().len(),
{
    if combiners.dom().len() == 0 {
        assert(combiner_request_ids(combiners).finite())
    } else {
        let node_id = combiners.dom().choose();
        assert(combiner_request_ids(combiners.remove(node_id)).finite()) by {
            combiner_request_ids_finite(combiners.remove(node_id));
        }
        assert(seq_to_set(combiners[node_id].queued_ops()).finite()) by {
            seq_to_set_is_finite(combiners[node_id].queued_ops());
        }
    }
}


// File: spec/utils.rs
pub open spec fn seq_to_set<A>(seq: Seq<A>) -> Set<A> {
    Set::new(|a: A| seq.contains(a))
}

	#[verifier::external_body]
pub proof fn seq_to_set_is_finite<A>(seq: Seq<A>)
    ensures
        seq_to_set(seq).finite(),
	{
		unimplemented!()
	}

}
