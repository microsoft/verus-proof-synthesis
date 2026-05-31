use vstd::prelude::*;

fn main() {}

verus!{

// File: userspace.rs
pub const FLAG_INITIALIZED: u8 = 0x01;

pub fn init_flags_decide(current_flags: u8) -> (result: u8)
    ensures
        result == (current_flags | FLAG_INITIALIZED),
        // US7a: INITIALIZED bit is always set in the result.
        (result & FLAG_INITIALIZED) == FLAG_INITIALIZED,
        // Monotonic: bits that were set remain set.
        (current_flags & result) == current_flags,
{
    let result = current_flags | FLAG_INITIALIZED;
    let flaginit = FLAG_INITIALIZED;
    result
}


}
