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

    pub open spec fn len_spec(&self) -> nat {
        self.len as nat
    }

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

	#[verifier::external_body]
    pub fn len(&self) -> (result: u32)
        requires
            self.inv(),
        ensures
            result == self.len,
	{
		unimplemented!()
	}

	#[verifier::external_body]
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
		unimplemented!()
	}

}



// File: futex.rs
#[derive(Debug)]
pub struct WakeResult {
    /// Number of threads woken.
    pub woken: u32,
    /// The woken threads (up to MAX_WAITERS).
    /// Only the first `woken` entries are meaningful.
    pub threads: [Option<Thread>; 64],
}

pub struct Futex {
    /// The 32-bit atomic value.
    /// Corresponds to futex->val.
    pub val: u32,
    /// Wait queue for threads blocked on this futex.
    /// Corresponds to futex_data->wait_q.
    pub wait_q: WaitQueue,
}

impl Futex {

    pub open spec fn inv(&self) -> bool {
        self.wait_q.inv()
    }

    pub fn wake(&mut self, wake_all: bool) -> (result: WakeResult)
        requires
            old(self).inv(),
        ensures
            self.inv(),
            self.val == old(self).val,
            // FX3: woken count is correct
            result.woken <= old(self).wait_q.len_spec(),
            // FX4: wake_all=false wakes at most 1
            !wake_all ==> result.woken <= 1,
            // FX5: wake_all=true wakes all waiters
            wake_all ==> {
                &&& result.woken == old(self).wait_q.len_spec()
                &&& self.wait_q.len_spec() == 0
            },
            // FX4 (continued): if !wake_all and there were waiters, exactly 1 woken
            !wake_all && old(self).wait_q.len_spec() > 0 ==> {
                &&& result.woken == 1
                &&& self.wait_q.len_spec() == old(self).wait_q.len_spec() - 1
            },
            // No waiters: woken == 0
            old(self).wait_q.len_spec() == 0 ==> result.woken == 0,
            // FX6: woken fits in u32 (trivially true since MAX_WAITERS = 64)
            result.woken <= MAX_WAITERS,
    {
        let mut woken: u32 = 0;
        let mut threads: [Option<Thread>; 64] = [
            None, None, None, None, None, None, None, None,
            None, None, None, None, None, None, None, None,
            None, None, None, None, None, None, None, None,
            None, None, None, None, None, None, None, None,
            None, None, None, None, None, None, None, None,
            None, None, None, None, None, None, None, None,
            None, None, None, None, None, None, None, None,
            None, None, None, None, None, None, None, None,
        ];

        // do { ... } while (thread && wake_all);
        // Model as: wake one, then if wake_all, wake remaining.
        if !wake_all {
            // Wake at most one thread.
            let thread = self.wait_q.unpend_first(OK);
            match thread {
                Some(t) => {
                    threads[0] = Some(t);
                    woken = 1;
                }
                None => {
                    // No waiters — woken stays 0.
                }
            }
        } else {
            // Wake all waiters.
            let count = self.wait_q.len();
            let mut i: u32 = 0;
            while i < count
                invariant
                    0 <= i <= count,
                    count == old(self).wait_q.len_spec(),
                    count <= MAX_WAITERS,
                    self.inv(),
                    self.val == old(self).val,
                    woken == i,
                    self.wait_q.len_spec() == (count - i) as nat,
                decreases
                    count - i,
            {
                let thread = self.wait_q.unpend_first(OK);
                match thread {
                    Some(t) => {
                        threads[i as usize] = Some(t);
                        woken = woken + 1;
                    }
                    None => {
                        // Should not happen within i < count, but safe.
                    }
                }
                i = i + 1;
            }
        }

        WakeResult { woken, threads }
    }

}



// File: error.rs
pub const OK: i32 = 0;


}
