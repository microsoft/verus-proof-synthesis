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

    pub fn unpend_first(&mut self, return_value: i32) -> (result: Option<Thread>)
        requires
            old(self).inv(),
        ensures
            self.inv(),
            old(self).len == 0 ==> result.is_none() && self.len == old(self).len,
            old(self).len > 0 ==> {
                &&& result.is_some()
                &&& self.len == old(self).len - 1
                &&& result.unwrap().state === ThreadState::Ready
                &&& result.unwrap().return_value == return_value
                &&& result.unwrap().inv()
            },
    {
        if self.len == 0 {
            return None;
        }

        // Take the first thread (highest priority).
        let thread = self.entries[0];
        self.entries[0] = None;

        // Shift remaining entries down by one.
        let mut i: u32 = 0;
        while i < self.len - 1
            invariant
                0 <= i <= self.len - 1,
                self.len == old(self).len,
                self.len <= MAX_WAITERS,
                self.len > 0,
                // Shifted portion: entries[0..i) contain old entries[1..i+1)
                forall|k: int| 0 <= k < i as int
                    ==> (#[trigger] self.entries[k]) === old(self).entries[k + 1],
                // Current position is None
                (#[trigger] self.entries[i as int]).is_none(),
                // Unshifted portion: entries[i+1..len) unchanged
                forall|k: int| (i as int) + 1 <= k < self.len as int
                    ==> (#[trigger] self.entries[k]) === old(self).entries[k],
                // Tail is None
                forall|k: int| self.len as int <= k < 64
                    ==> (#[trigger] self.entries[k]).is_none(),
                // Thread saved from position 0
                thread === old(self).entries[0int],
            decreases
                self.len - 1 - i,
        {
            self.entries[i as usize] = self.entries[(i + 1) as usize];
            self.entries[(i + 1) as usize] = None;
            i = i + 1;
        }

        // After shift: entries[0..len-2] == old entries[1..len-1], entries[len-1..63] are None.
        // Hint: all entries in [0, len-1) match old entries shifted by 1.
        assert(forall|k: int| 0 <= k < (self.len - 1) as int
            ==> (#[trigger] self.entries[k]) === old(self).entries[k + 1]);

        self.len = self.len - 1;

        // Prove slots_valid: occupied slots [0..new_len) are Some, rest are None.
        assert(forall|k: int| 0 <= k < self.len as int
            ==> (#[trigger] self.entries[k]).is_some());
        assert(forall|k: int| self.len as int <= k < 64
            ==> (#[trigger] self.entries[k]).is_none());

        // Prove is_sorted: shifted entries preserve original ordering.
        assert(forall|i1: int, j1: int| 0 <= i1 < j1 < self.len as int
            ==> (#[trigger] self.entries[i1]).is_some()
            && (#[trigger] self.entries[j1]).is_some()
            && self.entries[i1].unwrap().priority.view()
                <= self.entries[j1].unwrap().priority.view());

        // Prove threads_valid: all threads are valid and Blocked.
        assert(forall|k: int| 0 <= k < self.len as int
            ==> (#[trigger] self.entries[k]).is_some()
            && self.entries[k].unwrap().inv()
            && self.entries[k].unwrap().state === ThreadState::Blocked);

        // Prove no_duplicates: subset of original, no new IDs introduced.
        assert(forall|i1: int, j1: int| 0 <= i1 < j1 < self.len as int
            ==> (#[trigger] self.entries[i1]).is_some()
            && (#[trigger] self.entries[j1]).is_some()
            && self.entries[i1].unwrap().id.id
                != self.entries[j1].unwrap().id.id);

        // Set the thread's state to Ready with the return value.
        match thread {
            Some(mut t) => {
                t.state = ThreadState::Ready;
                t.return_value = return_value;
                Some(t)
            }
            None => None,
        }
    }

}



}
