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
    // Verus's SMT layer doesn't multiply variables by constants on its
    // own. Same idiom as systick::ticks_to_cycles_checked uses
    // (lemma_mul_inequality from vstd::arithmetic::mul).
    //
    // chunks ≤ MAX_CHUNKS ⇒
    //   chunks * CHUNK_TRAILER_BYTES ≤ MAX_CHUNKS * CHUNK_TRAILER_BYTES
    //   = 65535 * 8 = 524280 ≤ u32::MAX (4_294_967_295).
    use vstd::arithmetic::mul::lemma_mul_inequality;

    lemma_mul_inequality(
        chunks as int,
        MAX_CHUNKS as int,
        CHUNK_TRAILER_BYTES as int,
    );
    assert((MAX_CHUNKS as int) * (CHUNK_TRAILER_BYTES as int) == 524280int);
    assert((chunks as int) * (CHUNK_TRAILER_BYTES as int) <= 524280int);
    assert((CHUNK_TRAILER_BYTES as u64) * (chunks as u64) <= 524280u64);
    assert(524280u64 <= u32::MAX as u64);
}


}
