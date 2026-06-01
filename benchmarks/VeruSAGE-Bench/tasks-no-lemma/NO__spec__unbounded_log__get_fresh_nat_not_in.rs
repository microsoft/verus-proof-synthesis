use vstd::prelude::*;

fn main() {}
pub type ReqId=nat;
pub type NodeId=nat;
pub type LogIdx=nat;

verus!{

pub open spec fn seq_to_set<A>(seq: Seq<A>) -> Set<A> {
    Set::new(|a: A| seq.contains(a))
}

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

pub open spec fn combiner_request_id_fresh(
    combiners: Map<NodeId, CombinerState>,
    rid: ReqId,
) -> bool {
    forall|n| (#[trigger] combiners.contains_key(n)) ==> !combiners[n].queued_ops().contains(rid)
}


pub closed spec fn get_fresh_nat(reqs: Set<ReqId>, combiner: Map<NodeId, CombinerState>) -> nat
    recommends
        reqs.finite() && combiner.dom().finite(),
{
    choose|n| !reqs.contains(n) && combiner_request_id_fresh(combiner, n)
}

pub proof fn get_fresh_nat_not_in(reqs: Set<ReqId>, combiner: Map<NodeId, CombinerState>)
    requires
        reqs.finite(),
        combiner.dom().finite(),
    ensures
        !reqs.contains(get_fresh_nat(reqs, combiner)),
        combiner_request_id_fresh(combiner, get_fresh_nat(reqs, combiner)),
{
}
}
