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

	#[verifier::external_body]
#[verifier::external_body]
fn poll_events_set_state(events: &mut [PollEvent; 16], idx: usize, state: u32) {
		unimplemented!()
	}


impl PollEvents {

    pub open spec fn inv(&self) -> bool {
        self.num_events <= MAX_POLL_EVENTS
    }

    pub fn reset_all_states(&mut self)
        requires old(self).inv(),
        ensures
            self.inv(),
            self.num_events == old(self).num_events,
    {
        let mut i: u32 = 0;
        while i < self.num_events
            invariant
                0 <= i <= self.num_events,
                self.num_events == old(self).num_events,
                self.num_events <= MAX_POLL_EVENTS,
            decreases self.num_events - i,
        {
            poll_events_set_state(&mut self.events, i as usize, STATE_NOT_READY);
            i = i + 1;
        }
    }

}



}
