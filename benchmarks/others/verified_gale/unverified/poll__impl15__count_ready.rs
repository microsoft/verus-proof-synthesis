use vstd::prelude::*;

fn main() {}

verus!{

// File: poll.rs
pub const STATE_NOT_READY: u32 = 0;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct PollEvent {
    /// Bitfield of event types (K_POLL_TYPE_xxx).
    pub event_type: u32,
    /// Bitfield of event states (K_POLL_STATE_xxx).
    pub state: u32,
    /// Optional user-specified tag (opaque, untouched by API).
    pub tag: u32,
}

pub const MAX_POLL_EVENTS: u32 = 16;

#[derive(Debug)]
pub struct PollEvents {
    /// Events array.
    pub events: [PollEvent; 16],
    /// Number of active events (0..=MAX_POLL_EVENTS).
    pub num_events: u32,
}

impl PollEvents {

    pub open spec fn inv(&self) -> bool {
        self.num_events <= MAX_POLL_EVENTS
    }

    pub fn count_ready(&self) -> (result: u32)
        requires self.inv(),
    {
        let mut i: u32 = 0;
        let mut count: u32 = 0;
        while i < self.num_events
        {
            if self.events[i as usize].state != STATE_NOT_READY {
                count = count + 1;
            }
            i = i + 1;
        }
        count
    }

}



}
