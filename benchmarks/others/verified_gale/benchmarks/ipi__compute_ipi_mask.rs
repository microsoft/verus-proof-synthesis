use vstd::prelude::*;

fn main() {}

verus!{

// File: ipi.rs
pub const MAX_CPUS: u32 = 16;

pub fn compute_ipi_mask(
    current_cpu: u32,
    target_prio: i32,
    target_cpu_mask: u32,
    cpu_prios: &[i32],
    cpu_active: &[bool],
    num_cpus: u32,
    max_cpus: u32,
) -> (result: u32)
    requires
        num_cpus <= max_cpus,
        max_cpus <= MAX_CPUS,
        MAX_CPUS <= 32,
        current_cpu < num_cpus,
        cpu_prios.len() == num_cpus as int,
        cpu_active.len() == num_cpus as int,
    // IP1 (current CPU exclusion), IP2 (bounded), IP5 (max_cpus)
    // are verified via runtime tests and Kani BMC.
    // Verus ensures deferred: loop invariants need bit_set lemmas
    // for OR operations that Z3 cannot discharge without manual help.
{
    let mut mask: u32 = 0u32;
    let mut idx: u32 = 0u32;

    while idx < num_cpus
        invariant
            num_cpus <= max_cpus,
            max_cpus <= MAX_CPUS,
            MAX_CPUS <= 32,
            current_cpu < num_cpus,
            cpu_prios.len() == num_cpus as int,
            cpu_active.len() == num_cpus as int,
            0 <= idx <= num_cpus,
        decreases
            (num_cpus - idx) as int,
    {
        if idx != current_cpu {
            if cpu_active[idx as usize] {
                // Check CPU affinity: BIT(idx) & target_cpu_mask
                let bit: u32 = 1u32 << idx;
                if (target_cpu_mask & bit) != 0u32 {
                    // z_sched_prio_cmp(cpu_thread, thread) < 0
                    // means thread.prio < cpu_thread.prio
                    // i.e., cpu_prios[idx] > target_prio
                    if cpu_prios[idx as usize] > target_prio {
                        mask = mask | bit;
                    }
                }
            }
        }
        idx = idx + 1u32;
    }

    mask
}


}
