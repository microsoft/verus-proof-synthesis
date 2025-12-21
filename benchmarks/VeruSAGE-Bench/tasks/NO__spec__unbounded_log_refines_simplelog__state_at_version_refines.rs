use vstd::prelude::*;
use crate::lib::Dispatch;
use crate::types::LogEntry;

fn main() {}
pub type LogIdx = nat;

verus!{

// File: spec/types.rs
mod types{
  use vstd::prelude::*;
  pub type NodeId = nat;
  use crate::lib::Dispatch;

  /// This represents an entry in the abstract log
  pub tracked struct LogEntry<DT: Dispatch> {
    pub op: DT::WriteOperation,
    pub node_id: NodeId,
  }
}

// File: spec/simple_log.rs
mod simple_log {
  use vstd::prelude::*;
  use crate::lib::Dispatch;

  pub type LogIdx = nat;

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
}

// File: spec/unbounded_log.rs
mod unbounded_log {
  use vstd::prelude::*;
  use crate::lib::Dispatch;
  use crate::types::LogEntry;

  pub type LogIdx = nat;

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
}

#[cfg(verus_keep_ghost)]
use simple_log::{
    compute_nrstate_at_version as s_nrstate_at_version, 
};
#[cfg(verus_keep_ghost)]
use unbounded_log::{
    compute_nrstate_at_version as i_nrstate_at_version,
};

// File: lib.rs
mod lib {
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
}

// File: spec/unbounded_log_refines_simplelog.rs
spec fn interp_log<DT: Dispatch>(global_tail: nat, log: Map<nat, LogEntry<DT>>) -> Seq<
    DT::WriteOperation,
> {
    Seq::new(global_tail, |i| log.index(i as nat).op)
}

proof fn state_at_version_refines<DT: Dispatch>(
    s_log: Seq<DT::WriteOperation>,
    i_log: Map<LogIdx, LogEntry<DT>>,
    gtail: nat,
    idx: nat,
)
    requires
        forall|i| 0 <= i < gtail ==> i_log.contains_key(i),
        0 <= idx <= s_log.len(),
        idx <= gtail,
        s_log == interp_log(gtail, i_log),
    ensures
        s_nrstate_at_version::<DT>(s_log, idx) == i_nrstate_at_version::<DT>(i_log, idx),
{
}
}
