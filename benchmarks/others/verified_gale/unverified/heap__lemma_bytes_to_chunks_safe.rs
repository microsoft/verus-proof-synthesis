use vstd::prelude::*;

fn main() {}

verus!{

// File: heap.rs
pub const CHUNK_UNIT: u32 = 8;

pub proof fn lemma_bytes_to_chunks_safe(bytes: u32)
    ensures
        (bytes as u64 + CHUNK_UNIT as u64 - 1) / (CHUNK_UNIT as u64 as int) <= u32::MAX as u64,
{
}


}
