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

proof fn LogRangeMatchesQueue_append_other_augment<DT: Dispatch>(
    queue: Seq<nat>,
    log: Map<nat, LogEntry<DT>>,
    new_log: Map<nat, LogEntry<DT>>,
    queueIndex: nat,
    logIndexLower: nat,
    logIndexUpper: nat,
    node_id: NodeId,
    updates: Map<ReqId, UpdateState<DT>>,
    new_updates: Map<ReqId, UpdateState<DT>>,
    new_rid: ReqId,
    log_entry: LogEntry<DT>,
)
    requires
        0 <= queueIndex <= queue.len(),
        logIndexLower <= logIndexUpper,
        log_entry.node_id != node_id,
        new_updates.contains_key(new_rid),
        new_updates.index(new_rid) === (UpdateState::Placed {
            op: log_entry.op,
            idx: logIndexUpper,
        }),
        !queue.contains(new_rid),
        forall|rid| #[trigger]
            updates.contains_key(rid) && rid != new_rid ==> new_updates.contains_key(rid)
                && new_updates[rid] === updates[rid],
        LogRangeMatchesQueue(
            queue,
            log,
            queueIndex,
            logIndexLower,
            logIndexUpper,
            node_id,
            updates,
        ),
        new_log === log.insert(logIndexUpper, log_entry),
    ensures
        LogRangeMatchesQueue(
            queue,
            new_log,
            queueIndex,
            logIndexLower,
            logIndexUpper + 1,
            node_id,
            new_updates,
        ),
    decreases (logIndexUpper - logIndexLower),
{
    if logIndexLower == logIndexUpper + 1 {
    } else if logIndexLower == logIndexUpper {
        assert(new_log.contains_key(logIndexLower));
        assert(new_log.index(logIndexLower).node_id != node_id);
        assert(LogRangeMatchesQueue(
            queue,
            new_log,
            queueIndex,
            logIndexLower + 1,
            logIndexUpper + 1,
            node_id,
            new_updates,
        ));
    } else {
        assert(new_log.index(logIndexLower) === log.index(logIndexLower));
        if new_log.index(logIndexLower).node_id == node_id {
            LogRangeMatchesQueue_append_other_augment(
                queue,
                log,
                new_log,
                queueIndex + 1,
                logIndexLower + 1,
                logIndexUpper,
                node_id,
                updates,
                new_updates,
                new_rid,
                log_entry,
            );
            assert(LogRangeMatchesQueue(
                queue,
                new_log,
                queueIndex,
                logIndexLower,
                logIndexUpper + 1,
                node_id,
                new_updates,
            ));
        } else {
            LogRangeMatchesQueue_append_other_augment(
                queue,
                log,
                new_log,
                queueIndex,
                logIndexLower + 1,
                logIndexUpper,
                node_id,
                updates,
                new_updates,
                new_rid,
                log_entry,
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
