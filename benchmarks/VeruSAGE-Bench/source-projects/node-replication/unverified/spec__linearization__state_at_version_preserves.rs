use vstd::prelude::*;

fn main() {}
pub type LogIdx = nat;

verus!{

// File: lib.rs
pub trait Dispatch: Sized {
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

// File: spec/simple_log.rs

/// constructs the state of the data structure at a specific version given the log
///
/// This function recursively applies the update operations to the initial state of the
/// data structure and returns the state of the data structure at the given version. The
/// version must be within the log's range.

pub open spec fn compute_nrstate_at_version<DT: Dispatch>(
    log: Seq<DT::WriteOperation>,
    version: LogIdx,
) -> DT::View
    recommends
        0 <= version <= log.len(),
    decreases version,
{
    if version == 0 {
        DT::init_spec()
    } else {
        DT::dispatch_mut_spec(
            compute_nrstate_at_version::<DT>(log, (version - 1) as nat),
            log[version - 1],
        ).0
    }
}



// File: spec/linearization.rs

proof fn state_at_version_preserves<DT: Dispatch>(
    a: Seq<DT::WriteOperation>,
    b: Seq<DT::WriteOperation>,
    x: DT::WriteOperation,
    i: LogIdx,
)
    requires
        b == a.push(x),
        i <= a.len(),
        i <= b.len(),
    ensures
        compute_nrstate_at_version::<DT>(a, i) == compute_nrstate_at_version::<DT>(b, i),
{
}


}
