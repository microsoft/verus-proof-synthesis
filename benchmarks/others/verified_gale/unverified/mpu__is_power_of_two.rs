use vstd::prelude::*;

fn main() {}

verus!{

// File: mpu.rs
pub open spec fn is_pow2_spec(n: u32) -> bool {
    n == 1u32 || n == 2u32 || n == 4u32 || n == 8u32
    || n == 16u32 || n == 32u32 || n == 64u32 || n == 128u32
    || n == 256u32 || n == 512u32 || n == 1024u32 || n == 2048u32
    || n == 4096u32 || n == 8192u32 || n == 16384u32 || n == 32768u32
    || n == 65536u32 || n == 131072u32 || n == 262144u32 || n == 524288u32
    || n == 1048576u32 || n == 2097152u32 || n == 4194304u32 || n == 8388608u32
    || n == 16777216u32 || n == 33554432u32 || n == 67108864u32 || n == 134217728u32
    || n == 268435456u32 || n == 536870912u32 || n == 1073741824u32 || n == 2147483648u32
}

pub fn is_power_of_two(n: u32) -> (result: bool)
    ensures
        result == is_pow2_spec(n),
{
    let result = n > 0 && (n & (n - 1)) == 0;
    result
}


}
