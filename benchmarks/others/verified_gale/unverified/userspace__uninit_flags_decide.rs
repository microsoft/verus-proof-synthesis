use vstd::prelude::*;

fn main() {}

verus!{

// File: userspace.rs
pub const FLAG_INITIALIZED: u8 = 0x01;

pub const FLAG_PUBLIC: u8 = 0x02;

pub fn uninit_flags_decide(current_flags: u8) -> (result: u8)
    ensures
        result == (current_flags & !FLAG_INITIALIZED),
        // US7b: INITIALIZED bit is cleared in the result.
        (result & FLAG_INITIALIZED) == 0u8,
        // Other bits (e.g. PUBLIC) are preserved.
        (result & FLAG_PUBLIC) == (current_flags & FLAG_PUBLIC),
{
    let result = current_flags & !FLAG_INITIALIZED;
    let flag_initialized = FLAG_INITIALIZED;


    result
}


}
