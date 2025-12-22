use vstd::prelude::*;

fn main() {}
pub type ReqId=nat;
pub type NodeId=nat;
pub type LogIdx=nat;

verus!{

// File: lib.rs
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
// File: spec/types.rs
/// This represents an entry in the abstract log
pub tracked struct LogEntry<DT: Dispatch> {
    pub op: DT::WriteOperation,
    pub node_id: NodeId,
}


// File: spec/unbounded_log.rs
/// constructs the state of the data structure at a specific version given the log
///
/// This function recursively applies the update operations to the initial state of the
/// data structure and returns the state of the data structure at the given version.
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
{
}
}
