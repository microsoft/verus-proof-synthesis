use vstd::prelude::*;

fn main() {}

verus!{

// File: heap.rs
pub const MAX_CHUNKS: u32 = 65535;

pub const CHUNK_TRAILER_BYTES: u32 = 8;

pub proof fn lemma_trailer_reserve_fits_u32(chunks: u32)
    requires chunks <= MAX_CHUNKS,
    ensures
        (CHUNK_TRAILER_BYTES as u64) * (chunks as u64) <= u32::MAX as u64,
{
}


}
