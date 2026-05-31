use vstd::prelude::*;

fn main() {}

verus!{

// File: userspace.rs
pub const FLAG_INITIALIZED: u8 = 0x01;

pub const FLAG_PUBLIC: u8 = 0x02;

pub fn make_public_flags_decide(current_flags: u8) -> (result: u8)
    ensures
        result == (current_flags | FLAG_PUBLIC),
        // US5: PUBLIC bit is always set in the result.
        (result & FLAG_PUBLIC) == FLAG_PUBLIC,
        // Monotonic: INITIALIZED (and other) bits are preserved.
        (result & FLAG_INITIALIZED) == (current_flags & FLAG_INITIALIZED),
{
    let result = current_flags | FLAG_PUBLIC;

    result
}


}
