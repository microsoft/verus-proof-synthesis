use vstd::prelude::*;

fn main() {}

verus!{

// File: priority.rs
pub const MAX_PRIORITY: u32 = 32;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Priority {
    pub value: u32,
}

impl Priority {

    pub open spec fn inv(&self) -> bool {
        self.value < MAX_PRIORITY
    }

    pub open spec fn view(&self) -> nat {
        self.value as nat
    }

}



// File: thread.rs
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct ThreadId {
    pub id: u32,
}

#[allow(dead_code)]
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ThreadState {
    /// Thread is ready to run (in the ready queue).
    Ready,
    /// Thread is the currently executing thread.
    Running,
    /// Thread is blocked on a kernel object (semaphore, mutex, etc).
    /// Stores the return value that will be set when unblocked.
    Blocked,
    /// Thread is suspended (not schedulable until explicitly resumed).
    Suspended,
}

#[derive(Debug, Copy, Clone)]
pub struct Thread {
    /// Unique identifier.
    pub id: ThreadId,
    /// Static priority (lower value = higher priority).
    pub priority: Priority,
    /// Current execution state.
    pub state: ThreadState,
    /// Return value set by kernel when unblocking this thread.
    /// Corresponds to arch_thread_return_value_set() in Zephyr.
    pub return_value: i32,
    /// Whether this thread has MetaIRQ priority.
    /// In Zephyr, MetaIRQ threads have priority < CONFIG_NUM_METAIRQ_PRIORITIES.
    /// Used by scheduler to decide preemption policy (SC6, SC9).
    pub is_metairq: bool,
}

impl Thread {

    pub open spec fn inv(&self) -> bool {
        self.priority.inv()
    }

}



// File: wait_queue.rs
pub const MAX_WAITERS: u32 = 64;

#[derive(Debug)]
pub struct WaitQueue {
    /// Threads waiting, sorted by priority (highest priority first).
    pub entries: [Option<Thread>; 64],
    /// Number of threads currently in the queue.
    pub len: u32,
}

impl WaitQueue {

    pub open spec fn is_sorted(&self) -> bool {
        forall|i: int, j: int|
            0 <= i < j < self.len as int
            ==> (#[trigger] self.entries[i]).is_some()
            && (#[trigger] self.entries[j]).is_some()
            && self.entries[i].unwrap().priority.view()
                <= self.entries[j].unwrap().priority.view()
    }

    pub open spec fn slots_valid(&self) -> bool {
        &&& forall|i: int| 0 <= i < self.len as int
                ==> (#[trigger] self.entries[i]).is_some()
        &&& forall|i: int| self.len as int <= i < 64
                ==> (#[trigger] self.entries[i]).is_none()
    }

    pub open spec fn threads_valid(&self) -> bool {
        forall|i: int| 0 <= i < self.len as int
            ==> (#[trigger] self.entries[i]).is_some()
            && self.entries[i].unwrap().inv()
            && self.entries[i].unwrap().state === ThreadState::Blocked
    }

    pub open spec fn no_duplicates(&self) -> bool {
        forall|i: int, j: int|
            0 <= i < j < self.len as int
            ==> (#[trigger] self.entries[i]).is_some()
            && (#[trigger] self.entries[j]).is_some()
            && self.entries[i].unwrap().id.id
                != self.entries[j].unwrap().id.id
    }

    pub open spec fn inv(&self) -> bool {
        &&& self.len <= MAX_WAITERS
        &&& self.slots_valid()
        &&& self.is_sorted()
        &&& self.threads_valid()
        &&& self.no_duplicates()
    }

    pub fn unpend_all(&mut self, return_value: i32) -> (woken: u32)
        requires
            old(self).inv(),
        ensures
            self.inv(),
            self.len == 0,
            woken == old(self).len,
    {
        let count = self.len;
        let mut i: u32 = 0;
        while i < count
        {
            self.entries[i as usize] = None;
            i = i + 1;
        }
        self.len = 0;
        count
    }

}



}
