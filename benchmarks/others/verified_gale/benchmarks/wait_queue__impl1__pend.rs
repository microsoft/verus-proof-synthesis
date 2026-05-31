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

	#[verifier::external_body]
    pub fn get(&self) -> (result: u32)
        requires
            self.inv(),
        ensures
            result == self.value,
            result < MAX_PRIORITY,
	{
		unimplemented!()
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

    pub fn pend(&mut self, thread: Thread) -> (result: bool)
        requires
            old(self).inv(),
            thread.inv(),
            thread.state === ThreadState::Blocked,
            old(self).len < MAX_WAITERS,
            // New thread's ID must not already be in the queue.
            forall|k: int| 0 <= k < old(self).len as int
                ==> (#[trigger] old(self).entries[k]).is_some()
                && old(self).entries[k].unwrap().id.id != thread.id.id,
        ensures
            self.inv(),
            result == true,
            self.len == old(self).len + 1,
    {
        if self.len >= MAX_WAITERS {
            // Precondition guarantees old(self).len < MAX_WAITERS,
            // so this branch is unreachable.
            return false;
        }

        // Find insertion point: first entry with lower priority (higher value).
        let mut insert_pos: u32 = self.len;
        let mut i: u32 = 0;
        let mut found: bool = false;
        while i < self.len && !found
            invariant
                0 <= i <= self.len,
                self.len < MAX_WAITERS,
                self.len == old(self).len,
                self.inv(),
                // Queue unchanged during search
                forall|k: int| 0 <= k < 64
                    ==> (#[trigger] self.entries[k]) === old(self).entries[k],
                // Found state tracking
                !found ==> insert_pos == self.len,
                found ==> insert_pos == i && insert_pos < self.len,
                // When found: entry at insert_pos has priority > thread
                found ==> self.entries[insert_pos as int].is_some()
                    && thread.priority.view()
                        < self.entries[insert_pos as int].unwrap().priority.view(),
                // All entries before current scan position have priority <= thread
                forall|k: int| 0 <= k < i as int
                    ==> (#[trigger] self.entries[k]).is_some()
                    && self.entries[k].unwrap().priority.view()
                        <= thread.priority.view(),
                // Thread invariant preserved (not modified by loop)
                thread.inv(),
                thread.priority.inv(),
            decreases
                (self.len - i) * 2 + if !found { 1int } else { 0int },
        {
            // Access priority directly to help the solver with preconditions.
            let entry_pri = self.entries[i as usize].unwrap().priority.get();
            let thr_pri = thread.priority.get();
            if thr_pri < entry_pri {
                insert_pos = i;
                found = true;
            }
            if !found {
                i = i + 1;
            }
        }

        // After search: insert_pos is the correct insertion point.
        // entries[0..insert_pos) have priority <= thread.priority.

        // Shift entries from insert_pos to len-1 right by one.
        let mut j: u32 = self.len;
        while j > insert_pos
            invariant
                insert_pos <= j <= self.len,
                self.len < MAX_WAITERS,
                self.len == old(self).len,
                0 <= insert_pos <= self.len,
                // Entries before insert_pos unchanged
                forall|k: int| 0 <= k < insert_pos as int
                    ==> (#[trigger] self.entries[k]) === old(self).entries[k],
                // Entries between insert_pos and j unchanged
                forall|k: int| insert_pos as int <= k < j as int
                    ==> (#[trigger] self.entries[k]) === old(self).entries[k],
                // Position j is None
                (#[trigger] self.entries[j as int]).is_none(),
                // Shifted portion: entries[j+1..len+1) are old entries[j..len)
                forall|k: int| (j as int) + 1 <= k <= self.len as int
                    ==> (#[trigger] self.entries[k]) === old(self).entries[k - 1],
                // Tail beyond len+1 is None
                forall|k: int| (self.len as int) + 1 <= k < 64
                    ==> (#[trigger] self.entries[k]).is_none(),
            decreases
                j - insert_pos,
        {
            self.entries[j as usize] = self.entries[(j - 1) as usize];
            self.entries[(j - 1) as usize] = None;
            j = j - 1;
        }

        // After shift: entries[insert_pos] is None, ready for insertion.
        // entries[0..insert_pos) = original, entries[insert_pos+1..len+1) = old shifted.

        // Insert the thread at the correct position.
        self.entries[insert_pos as usize] = Some(thread);
        self.len = self.len + 1;

        // Prove slots_valid: [0..new_len) are Some, [new_len..64) are None.
        assert(forall|k: int| 0 <= k < self.len as int
            ==> (#[trigger] self.entries[k]).is_some());
        assert(forall|k: int| self.len as int <= k < 64
            ==> (#[trigger] self.entries[k]).is_none());

        // Prove threads_valid.
        assert(forall|k: int| 0 <= k < self.len as int
            ==> (#[trigger] self.entries[k]).is_some()
            && self.entries[k].unwrap().inv()
            && self.entries[k].unwrap().state === ThreadState::Blocked);

        // Prove is_sorted: break into cases around insert_pos.
        // Case 1: both indices < insert_pos (original entries, unchanged, sorted).
        // Case 2: i1 < insert_pos, j1 == insert_pos (entry[i1] <= thread).
        // Case 3: i1 == insert_pos, j1 > insert_pos (thread <= shifted entry).
        // Case 4: both indices > insert_pos (shifted from originals, sorted).
        assert(forall|i1: int, j1: int| 0 <= i1 < j1 < self.len as int
            ==> (#[trigger] self.entries[i1]).is_some()
            && (#[trigger] self.entries[j1]).is_some()
            && self.entries[i1].unwrap().priority.view()
                <= self.entries[j1].unwrap().priority.view());

        // Prove no_duplicates.
        assert(forall|i1: int, j1: int| 0 <= i1 < j1 < self.len as int
            ==> (#[trigger] self.entries[i1]).is_some()
            && (#[trigger] self.entries[j1]).is_some()
            && self.entries[i1].unwrap().id.id
                != self.entries[j1].unwrap().id.id);

        true
    }

}



}
