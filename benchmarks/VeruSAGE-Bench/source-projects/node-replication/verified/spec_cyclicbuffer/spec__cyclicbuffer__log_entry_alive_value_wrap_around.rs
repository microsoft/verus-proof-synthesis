use vstd::prelude::*;

fn main() {}

pub type NodeId = nat;
pub type LogicalLogIdx = int;

verus!{

// File: spec/cyclicbuffer.rs
pub open spec fn log_entry_alive_value(logical: LogicalLogIdx, buffer_size: nat) -> bool
    recommends
        buffer_size == LOG_SIZE,
{
    ((logical / buffer_size as int) % 2) == 0
}

pub proof fn log_entry_alive_value_wrap_around(i: LogicalLogIdx, buffer_size: nat)
    requires
        buffer_size > 0,
    ensures
        log_entry_alive_value(i, buffer_size) != log_entry_alive_value(
            i + (buffer_size as int),
            buffer_size,
        ),
{
    assert(((i + (buffer_size as int)) / buffer_size as int) == ((i / buffer_size as int) + 1)) by (nonlinear_arith)
        requires buffer_size > 0;
}


// File: constants.rs
pub open const LOG_SIZE: usize = 512 * 1024;


}
