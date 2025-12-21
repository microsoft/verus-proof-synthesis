use vstd::prelude::*;
verus! {

pub struct PersistentMemoryByte {
    pub state_at_last_flush: u8,
    pub outstanding_write: Option<u8>,
}

pub struct PersistentMemoryRegionView {
    pub state: Seq<PersistentMemoryByte>,
}

impl PersistentMemoryRegionView {
    pub open spec fn len(self) -> nat {
        self.state.len()
    }
}

pub struct PersistentMemoryConstants {
    pub impervious_to_corruption: bool,
}

pub trait PersistentMemoryRegion: Sized {
    spec fn view(&self) -> PersistentMemoryRegionView;

    spec fn inv(&self) -> bool;

    spec fn constants(&self) -> PersistentMemoryConstants;
}

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

pub struct WriteRestrictedPersistentMemorySubregion {
    start_: u64,
    len_: Ghost<nat>,
    constants_: Ghost<PersistentMemoryConstants>,
    initial_region_view_: Ghost<PersistentMemoryRegionView>,
    is_writable_absolute_addr_fn_: Ghost<spec_fn(int) -> bool>,
}

pub struct PersistentMemorySubregion {
    start_: u64,
    len_: Ghost<nat>,
}

pub struct WritablePersistentMemorySubregion {
    start_: u64,
    len_: Ghost<nat>,
    constants_: Ghost<PersistentMemoryConstants>,
    initial_region_view_: Ghost<PersistentMemoryRegionView>,
    is_writable_absolute_addr_fn_: Ghost<spec_fn(int) -> bool>,
}

impl WriteRestrictedPersistentMemorySubregion {
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

    pub closed spec fn initial_subregion_view(self) -> PersistentMemoryRegionView {
        get_subregion_view(self.initial_region_view(), self.start(), self.len())
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

    #[verifier::auto_ext_equal(assert, assert_by, ensures)]
    pub exec fn new<PMRegion: PersistentMemoryRegion>(
        pm: &PMRegion,
        start: u64,
        Ghost(len): Ghost<nat>,
        Ghost(is_writable_absolute_addr_fn): Ghost<spec_fn(int) -> bool>,
    ) -> (result: Self)
        requires
            pm.inv(),
            0 <= len,
            start + len <= pm@.len() <= u64::MAX,
        ensures
            result.inv(pm),
            result.constants() == pm.constants(),
            result.start() == start,
            result.len() == len,
            result.initial_region_view() == pm@,
            result.is_writable_absolute_addr_fn() == is_writable_absolute_addr_fn,
            result.view(pm) == result.initial_subregion_view(),
            result.view(pm) == get_subregion_view(pm@, start as nat, len),
    {
        let ghost self_ghost0: nat = arbitrary(); // TODO - replace with correct value
        let ghost self_ghost1: PersistentMemoryConstants = arbitrary(); // TODO - replace with correct value
        let ghost self_ghost2: PersistentMemoryRegionView = arbitrary(); // TODO - replace with correct value
        let ghost self_ghost3: spec_fn(int) -> bool = arbitrary(); // TODO - replace with correct value
        let result = Self {
            start_: start,
            len_: Ghost(self_ghost0),
            constants_: Ghost(self_ghost1),
            initial_region_view_: Ghost(self_ghost2),
            is_writable_absolute_addr_fn_: Ghost(self_ghost3),
        };
        result
    }
}

pub fn main() {
}

} // verus!
