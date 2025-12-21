use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

verus! {

pub fn main() {
}

/*pmem\pmemspect_t*/

pub struct PersistentMemoryByte {
    pub state_at_last_flush: u8,
    pub outstanding_write: Option<u8>,
}

impl PersistentMemoryByte {
    pub open spec fn flush_byte(self) -> u8 {
        match self.outstanding_write {
            None => self.state_at_last_flush,
            Some(b) => b,
        }
    }

    pub open spec fn flush(self) -> Self {
        Self { state_at_last_flush: self.flush_byte(), outstanding_write: None }
    }
}

#[verifier::ext_equal]
pub struct PersistentMemoryRegionView {
    pub state: Seq<PersistentMemoryByte>,
}

impl PersistentMemoryRegionView {
    pub open spec fn flush(self) -> Self {
        Self { state: self.state.map(|_addr, b: PersistentMemoryByte| b.flush()) }
    }

    pub open spec fn no_outstanding_writes_in_range(self, i: int, j: int) -> bool {
        forall|k| i <= k < j ==> (#[trigger] self.state[k].outstanding_write).is_none()
    }

    pub open spec fn no_outstanding_writes(self) -> bool {
        Self::no_outstanding_writes_in_range(self, 0, self.state.len() as int)
    }
}

#[verifier::ext_equal]
pub struct PersistentMemoryRegionsView {
    pub regions: Seq<PersistentMemoryRegionView>,
}

impl PersistentMemoryRegionsView {
    pub open spec fn len(self) -> nat {
        self.regions.len()
    }

    pub open spec fn spec_index(self, i: int) -> PersistentMemoryRegionView {
        self.regions[i]
    }

    pub open spec fn flush(self) -> Self {
        Self { regions: self.regions.map(|_pos, pm: PersistentMemoryRegionView| pm.flush()) }
    }

    pub open spec fn no_outstanding_writes(self) -> bool {
        forall|i: int| #![auto] 0 <= i < self.len() ==> self[i].no_outstanding_writes()
    }
}

pub trait PersistentMemoryRegion: Sized {

}

/*pmem\pmemutil_v*/

#[verifier::auto_ext_equal(assert, assert_by, ensures)]
pub proof fn lemma_auto_if_no_outstanding_writes_then_flush_is_idempotent()
    ensures
        forall|r: PersistentMemoryRegionsView| r.no_outstanding_writes() ==> r.flush() == r,
{
}

} // verus!
