use vstd::prelude::*;

fn main() {}

verus!{

// File: event.rs
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Event {
    /// Current 32-bit event bitmask.
    pub events: u32,
}

impl Event {

    pub open spec fn inv(&self) -> bool {
        true
    }

    pub fn post(&mut self, new_events: u32) -> (result: u32)
        requires old(self).inv(),
        ensures
            self.inv(),
            // EV1: post ORs bits
            self.events == (old(self).events | new_events),
            result == self.events,
            // EV8: post is monotonic — old bits are preserved
            old(self).events & self.events == old(self).events,
    {
        let old_events = self.events;
        self.events = self.events | new_events;
        let new_val = self.events;
        assert(old_events & new_val == old_events) by (bit_vector)
            requires new_val == (old_events | new_events);
        self.events
    }

}



}
