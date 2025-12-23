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
    pub open spec fn write(self, byte: u8) -> Self {
        Self { state_at_last_flush: self.state_at_last_flush, outstanding_write: Some(byte) }
    }
}

#[verifier::ext_equal]
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

    pub open spec fn no_outstanding_writes_in_range(self, i: int, j: int) -> bool {
        forall|k| i <= k < j ==> (#[trigger] self.state[k].outstanding_write).is_none()
    }
}

#[verifier::ext_equal]
pub struct PersistentMemoryConstants {
    pub impervious_to_corruption: bool,
}

pub trait PersistentMemoryRegion: Sized {
    spec fn view(&self) -> PersistentMemoryRegionView;

    spec fn inv(&self) -> bool;

    spec fn constants(&self) -> PersistentMemoryConstants;

    #[verifier::external_body]
    fn write(&mut self, addr: u64, bytes: &[u8])
        requires
            old(self).inv(),
            addr + bytes@.len() <= old(self)@.len(),
            addr + bytes@.len() <= u64::MAX,
            // Writes aren't allowed where there are already outstanding writes.
            old(self)@.no_outstanding_writes_in_range(addr as int, addr + bytes@.len()),
        ensures
            self.inv(),
            self.constants() == old(self).constants(),
            self@ == old(self)@.write(addr as int, bytes@),
    {
    }
}

/*pmem\subregion_v*/

pub open spec fn get_subregion_view(
    region: PersistentMemoryRegionView,
    start: nat,
    len: nat,
) -> PersistentMemoryRegionView
    recommends
        0 <= start,
        0 <= len,
        start + len <= region.len(),
{
    PersistentMemoryRegionView { state: region.state.subrange(start as int, (start + len) as int) }
}

pub open spec fn views_differ_only_where_subregion_allows(
    v1: PersistentMemoryRegionView,
    v2: PersistentMemoryRegionView,
    start: nat,
    len: nat,
    is_writable_absolute_addr_fn: spec_fn(int) -> bool,
) -> bool
    recommends
        0 <= start,
        0 <= len,
        start + len <= v1.len(),
        v1.len() == v2.len(),
{
    forall|addr: int|
        {
            ||| 0 <= addr < start
            ||| start + len <= addr < v1.len()
            ||| start <= addr < start + len && !is_writable_absolute_addr_fn(addr)
        } ==> v1.state[addr] == #[trigger] v2.state[addr]
}

#[verifier::ext_equal]
pub struct WriteRestrictedPersistentMemorySubregion {
    start_: u64,
    len_: Ghost<nat>,
    constants_: Ghost<PersistentMemoryConstants>,
    initial_region_view_: Ghost<PersistentMemoryRegionView>,
    is_writable_absolute_addr_fn_: Ghost<spec_fn(int) -> bool>,
}

#[verifier::ext_equal]
pub struct PersistentMemorySubregion {
    start_: u64,
    len_: Ghost<nat>,
}

#[verifier::ext_equal]
pub struct WritablePersistentMemorySubregion {
    start_: u64,
    len_: Ghost<nat>,
    constants_: Ghost<PersistentMemoryConstants>,
    initial_region_view_: Ghost<PersistentMemoryRegionView>,
    is_writable_absolute_addr_fn_: Ghost<spec_fn(int) -> bool>,
}

impl WritablePersistentMemorySubregion {
    pub closed spec fn constants(self) -> PersistentMemoryConstants {
        self.constants_@
    }

    pub closed spec fn start(self) -> nat {
        self.start_ as nat
    }

    pub closed spec fn len(self) -> nat {
        self.len_@
    }

    pub closed spec fn initial_region_view(self) -> PersistentMemoryRegionView {
        self.initial_region_view_@
    }

    pub closed spec fn is_writable_absolute_addr_fn(self) -> spec_fn(int) -> bool {
        self.is_writable_absolute_addr_fn_@
    }

    pub open spec fn is_writable_relative_addr(self, addr: int) -> bool {
        self.is_writable_absolute_addr_fn()(addr + self.start())
    }

    pub closed spec fn view<PMRegion: PersistentMemoryRegion>(
        self,
        pm: &PMRegion,
    ) -> PersistentMemoryRegionView {
        get_subregion_view(pm@, self.start(), self.len())
    }

    pub closed spec fn opaque_inv<PMRegion: PersistentMemoryRegion>(self, pm: &PMRegion) -> bool {
        &&& pm.inv()
        &&& pm.constants() == self.constants()
        &&& pm@.len() == self.initial_region_view().len()
        &&& self.initial_region_view().len() <= u64::MAX
        &&& self.start() + self.len() <= pm@.len()
        &&& self.view(pm).len() == self.len()
        &&& views_differ_only_where_subregion_allows(
            self.initial_region_view(),
            pm@,
            self.start(),
            self.len(),
            self.is_writable_absolute_addr_fn(),
        )
    }

    pub open spec fn inv<PMRegion: PersistentMemoryRegion>(self, pm: &PMRegion) -> bool {
        &&& self.view(pm).len() == self.len()
        &&& self.opaque_inv(pm)
    }

    pub exec fn write_relative<PMRegion: PersistentMemoryRegion>(
        self: &Self,
        pm: &mut PMRegion,
        relative_addr: u64,
        bytes: &[u8],
    )
        requires
            self.inv(old(pm)),
            relative_addr + bytes@.len() <= self.view(old(pm)).len(),
            self.view(old(pm)).no_outstanding_writes_in_range(
                relative_addr as int,
                relative_addr + bytes.len(),
            ),
            forall|i: int|
                relative_addr <= i < relative_addr + bytes@.len()
                    ==> self.is_writable_relative_addr(i),
        ensures
            self.inv(pm),
            self.view(pm) == self.view(old(pm)).write(relative_addr as int, bytes@),
    {
        let ghost subregion_view = self.view(pm).write(relative_addr as int, bytes@);
        assert(forall|addr|
            #![trigger self.is_writable_absolute_addr_fn()(addr)]
            !self.is_writable_absolute_addr_fn()(addr) ==> !self.is_writable_relative_addr(
                addr - self.start(),
            ));
        assert forall|i|
            #![trigger pm@.state[i]]
            relative_addr + self.start_ <= i < relative_addr + self.start_
                + bytes@.len() implies pm@.state[i].outstanding_write.is_none() by {
            assert(pm@.state[i] == self.view(pm).state[i - self.start()]);
        }
        pm.write(relative_addr + self.start_, bytes);
        assert(self.view(pm) =~= subregion_view);
    }
}

} // verus!
