use vstd::prelude::*;

fn main() {}

verus!{

// File: spinlock_validate.rs
pub const MAX_CPUS: u32 = 4;

pub const CPU_MASK: usize = 3; // MAX_CPUS - 1

pub open spec fn thread_ptr_valid(thread: usize) -> bool {
    thread != 0 && (thread & (CPU_MASK as usize)) == 0
}

pub open spec fn cpu_id_valid(cpu: u32) -> bool {
    (cpu as usize) < (MAX_CPUS as usize)
}

pub open spec fn encode_owner_spec(cpu: u32, thread: usize) -> usize {
    thread | (cpu as usize)
}

pub fn spin_lock_compute_owner(
    current_cpu_id: u32,
    current_thread: usize,
) -> (owner: usize)
    requires
        cpu_id_valid(current_cpu_id),
        thread_ptr_valid(current_thread),
    ensures
        owner == encode_owner_spec(current_cpu_id, current_thread),
{
    let cpu = current_cpu_id as usize;
    cpu | current_thread
}


}
