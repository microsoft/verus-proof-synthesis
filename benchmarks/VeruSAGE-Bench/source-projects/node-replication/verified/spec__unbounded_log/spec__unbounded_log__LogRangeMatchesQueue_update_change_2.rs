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

pub open spec fn LogContainsEntriesUpToHere<DT: Dispatch>(
    log: Map<LogIdx, LogEntry<DT>>,
    end: LogIdx,
) -> bool {
    forall|i: nat| 0 <= i < end ==> log.contains_key(i)
}

pub open spec fn LogRangeMatchesQueue<DT: Dispatch>(
    queue: Seq<ReqId>,
    log: Map<LogIdx, LogEntry<DT>>,
    queueIndex: nat,
    logIndexLower: LogIdx,
    logIndexUpper: LogIdx,
    nodeId: NodeId,
    updates: Map<ReqId, UpdateState<DT>>,
) -> bool {
    recommends([0 <= queueIndex <= queue.len(), LogContainsEntriesUpToHere(log, logIndexUpper)]);
    decreases_when(logIndexLower <= logIndexUpper);
    decreases(logIndexUpper - logIndexLower);
    // if we hit the end of the log range, we should be at the end of the queue
    &&& (logIndexLower == logIndexUpper ==> queueIndex
        == queue.len())
    // otherwise, we check the log

    &&& (logIndexLower < logIndexUpper ==> {
        &&& log.contains_key(
            logIndexLower,
        )
        // local case: the entry has been written by the local node

        &&& (log.index(logIndexLower).node_id == nodeId ==> {
            // there must be an entry in the queue that matches the log entry
            &&& queueIndex < queue.len()
            &&& updates.contains_key(queue.index(queueIndex as int))
            &&& updates.index(queue.index(queueIndex as int)) is Placed
            &&& updates.index(queue.index(queueIndex as int)).arrow_Placed_idx() == logIndexLower
            &&& LogRangeMatchesQueue(
                queue,
                log,
                queueIndex + 1,
                logIndexLower + 1,
                logIndexUpper,
                nodeId,
                updates,
            )
        })
        // remote case: the entry has been written by the local node, there is nothing to match, recourse

        &&& (log.index(logIndexLower).node_id != nodeId ==> LogRangeMatchesQueue(
            queue,
            log,
            queueIndex,
            logIndexLower + 1,
            logIndexUpper,
            nodeId,
            updates,
        ))
    })
}

proof fn LogRangeMatchesQueue_update_change_2<DT: Dispatch>(
    queue: Seq<nat>,
    log: Map<nat, LogEntry<DT>>,
    queueIndex: nat,
    logIndexLower: nat,
    logIndexUpper: nat,
    nodeId: nat,
    updates1: Map<ReqId, UpdateState<DT>>,
    updates2: Map<ReqId, UpdateState<DT>>,
)
    requires
        0 <= queueIndex <= queue.len(),
        logIndexLower <= logIndexUpper,
        LogRangeMatchesQueue(
            queue,
            log,
            queueIndex,
            logIndexLower,
            logIndexUpper,
            nodeId,
            updates1,
        ),
        forall|rid| #[trigger]
            updates1.contains_key(rid) ==> queue.contains(rid) ==> updates2.contains_key(rid)
                && updates2[rid] === updates1[rid],
    ensures
        LogRangeMatchesQueue(
            queue,
            log,
            queueIndex,
            logIndexLower,
            logIndexUpper,
            nodeId,
            updates2,
        ),
    decreases logIndexUpper - logIndexLower,
{
    if logIndexLower == logIndexUpper {
    } else {
        if log.index(logIndexLower).node_id == nodeId {
            LogRangeMatchesQueue_update_change_2(
                queue,
                log,
                queueIndex + 1,
                logIndexLower + 1,
                logIndexUpper,
                nodeId,
                updates1,
                updates2,
            );
        } else {
            LogRangeMatchesQueue_update_change_2(
                queue,
                log,
                queueIndex,
                logIndexLower + 1,
                logIndexUpper,
                nodeId,
                updates1,
                updates2,
            );
        }
    }
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
