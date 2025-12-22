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
pub open spec fn LogRangeNoNodeId<DT: Dispatch>(
    log: Map<LogIdx, LogEntry<DT>>,
    start: LogIdx,
    end: LogIdx,
    node_id: NodeId,
) -> bool {
    decreases_when(start <= end);
    decreases(end - start);
    (start < end ==> {
        &&& log.contains_key(start)
        &&& log.index(start).node_id != node_id
        &&& LogRangeNoNodeId(log, start + 1, end, node_id)
    })
}

proof fn LogRangeNoNodeId_append_other<DT: Dispatch>(
    log: Map<nat, LogEntry<DT>>,
    new_log: Map<nat, LogEntry<DT>>,
    logIndexLower: nat,
    logIndexUpper: nat,
    node_id: NodeId,
    log_entry: LogEntry<DT>,
)
    requires
        logIndexLower <= logIndexUpper,
        log_entry.node_id != node_id,
        LogRangeNoNodeId(log, logIndexLower, logIndexUpper, node_id),
        new_log === log.insert(logIndexUpper, log_entry),
    ensures
        LogRangeNoNodeId(new_log, logIndexLower, logIndexUpper + 1, node_id),
    decreases (logIndexUpper - logIndexLower),
{
    if logIndexLower == logIndexUpper + 1 {
    } else if logIndexLower == logIndexUpper {
        assert(new_log.contains_key(logIndexLower));
        assert(new_log[logIndexLower].node_id != node_id);
        assert(LogRangeNoNodeId(new_log, logIndexLower + 1, logIndexUpper + 1, node_id));
    } else {
        assert(new_log.index(logIndexLower) === log.index(logIndexLower));
        if new_log.index(logIndexLower).node_id == node_id {
            LogRangeNoNodeId_append_other(
                log,
                new_log,
                logIndexLower + 1,
                logIndexUpper,
                node_id,
                log_entry,
            );
            assert(LogRangeNoNodeId(new_log, logIndexLower, logIndexUpper + 1, node_id));
        } else {
            LogRangeNoNodeId_append_other(
                log,
                new_log,
                logIndexLower + 1,
                logIndexUpper,
                node_id,
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
