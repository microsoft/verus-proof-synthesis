use vstd::prelude::*;

fn main() {}

verus!{

// File: error.rs
pub const EINVAL: i32 = -22;


// File: cpu_mask.rs
pub open spec fn is_power_of_two(m: u32) -> bool {
    m == 1u32 || m == 2u32 || m == 4u32 || m == 8u32
    || m == 16u32 || m == 32u32 || m == 64u32 || m == 128u32
    || m == 256u32 || m == 512u32 || m == 1024u32 || m == 2048u32
    || m == 4096u32 || m == 8192u32 || m == 16384u32 || m == 32768u32
    || m == 65536u32 || m == 131072u32 || m == 262144u32 || m == 524288u32
    || m == 1048576u32 || m == 2097152u32 || m == 4194304u32 || m == 8388608u32
    || m == 16777216u32 || m == 33554432u32 || m == 67108864u32 || m == 134217728u32
    || m == 268435456u32 || m == 536870912u32 || m == 1073741824u32 || m == 2147483648u32
}

pub fn cpu_pin_compute(cpu_id: u32, max_cpus: u32) -> (result: Result<u32, i32>)
    ensures
        // Bounds failure
        (cpu_id >= max_cpus || max_cpus > 32) ==> result.is_err(),
        result.is_err() ==> result == Err::<u32, i32>(EINVAL),
        // Success: result is a single-bit mask
        result.is_ok() ==> {
            let m = result.unwrap();
            &&& cpu_id < 32
            &&& is_power_of_two(m)
        },
{
    if max_cpus > 32 || cpu_id >= max_cpus {
        return Err(EINVAL);
    }

    // cpu_id < 32 guaranteed by the bounds check above (max_cpus <= 32)
    let mask: u32 = 1u32 << cpu_id;

    Ok(mask)
}


}
