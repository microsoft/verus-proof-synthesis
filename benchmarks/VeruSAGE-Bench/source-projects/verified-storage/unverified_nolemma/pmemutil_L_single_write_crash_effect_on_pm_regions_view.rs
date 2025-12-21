use vstd::prelude::*;
verus! {

pub open spec fn const_persistence_chunk_size() -> int {
    8
}

pub struct PersistentMemoryByte {
    pub state_at_last_flush: u8,
    pub outstanding_write: Option<u8>,
}

impl PersistentMemoryByte {
    pub open spec fn write(self, byte: u8) -> Self {
        Self { state_at_last_flush: self.state_at_last_flush, outstanding_write: Some(byte) }
    }

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

pub struct PersistentMemoryRegionView {
    pub state: Seq<PersistentMemoryByte>,
}

impl PersistentMemoryRegionView {
    pub open spec fn len(self) -> nat {
        self.state.len()
    }

    pub open spec fn write(self, addr: int, bytes: Seq<u8>) -> Self {
        Self {
            state: self.state.map(
                |pos: int, pre_byte: PersistentMemoryByte|
                    if addr <= pos < addr + bytes.len() {
                        pre_byte.write(bytes[pos - addr])
                    } else {
                        pre_byte
                    },
            ),
        }
    }

    pub open spec fn flush(self) -> Self {
        Self { state: self.state.map(|_addr, b: PersistentMemoryByte| b.flush()) }
    }

    pub open spec fn no_outstanding_writes_in_range(self, i: int, j: int) -> bool {
        forall|k| i <= k < j ==> (#[trigger] self.state[k].outstanding_write).is_none()
    }

    pub open spec fn no_outstanding_writes(self) -> bool {
        Self::no_outstanding_writes_in_range(self, 0, self.state.len() as int)
    }

    pub open spec fn committed(self) -> Seq<u8> {
        self.state.map(|_addr, b: PersistentMemoryByte| b.state_at_last_flush)
    }

    pub open spec fn chunk_corresponds_ignoring_outstanding_writes(
        self,
        chunk: int,
        bytes: Seq<u8>,
    ) -> bool {
        forall|addr: int|
            {
                &&& 0 <= addr < self.len()
                &&& addr / const_persistence_chunk_size() == chunk
            } ==> #[trigger] bytes[addr] == self.state[addr].state_at_last_flush
    }

    pub open spec fn chunk_corresponds_after_flush(self, chunk: int, bytes: Seq<u8>) -> bool {
        forall|addr: int|
            {
                &&& 0 <= addr < self.len()
                &&& addr / const_persistence_chunk_size() == chunk
            } ==> #[trigger] bytes[addr] == self.state[addr].flush_byte()
    }

    pub open spec fn can_crash_as(self, bytes: Seq<u8>) -> bool {
        &&& bytes.len() == self.len()
        &&& forall|chunk|
            {
                ||| self.chunk_corresponds_ignoring_outstanding_writes(chunk, bytes)
                ||| self.chunk_corresponds_after_flush(chunk, bytes)
            }
    }
}

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

    pub open spec fn write(self, index: int, addr: int, bytes: Seq<u8>) -> Self {
        Self {
            regions: self.regions.map(
                |pos: int, pre_view: PersistentMemoryRegionView|
                    if pos == index {
                        pre_view.write(addr, bytes)
                    } else {
                        pre_view
                    },
            ),
        }
    }

    pub open spec fn flush(self) -> Self {
        Self { regions: self.regions.map(|_pos, pm: PersistentMemoryRegionView| pm.flush()) }
    }

    pub open spec fn no_outstanding_writes(self) -> bool {
        forall|i: int| #![auto] 0 <= i < self.len() ==> self[i].no_outstanding_writes()
    }

    pub open spec fn committed(self) -> Seq<Seq<u8>> {
        Seq::<Seq<u8>>::new(self.len(), |i: int| self[i].committed())
    }

    pub open spec fn can_crash_as(self, crash_regions: Seq<Seq<u8>>) -> bool {
        &&& crash_regions.len() == self.len()
        &&& forall|i: int| #![auto] 0 <= i < self.len() ==> self[i].can_crash_as(crash_regions[i])
    }
}

pub trait PersistentMemoryRegion: Sized {

}

pub fn main() {
}

#[verifier::auto_ext_equal(assert, assert_by, ensures)]
pub proof fn lemma_single_write_crash_effect_on_pm_regions_view(
    pm_regions_view: PersistentMemoryRegionsView,
    index: int,
    write_addr: int,
    bytes_to_write: Seq<u8>,
)
    requires
        0 <= index < pm_regions_view.len(),
        bytes_to_write.len() == const_persistence_chunk_size(),
        write_addr % const_persistence_chunk_size() == 0,
        0 <= write_addr,
        write_addr + const_persistence_chunk_size() <= pm_regions_view[index as int].len(),
        pm_regions_view.no_outstanding_writes(),
    ensures
        ({
            let new_pm_regions_view = pm_regions_view.write(index, write_addr, bytes_to_write);
            let flushed_pm_regions_view = new_pm_regions_view.flush();
            forall|crash_bytes: Seq<Seq<u8>>|
                new_pm_regions_view.can_crash_as(crash_bytes) ==> {
                    ||| crash_bytes == pm_regions_view.committed()
                    ||| crash_bytes == flushed_pm_regions_view.committed()
                }
        }),
{
}

} // verus!
