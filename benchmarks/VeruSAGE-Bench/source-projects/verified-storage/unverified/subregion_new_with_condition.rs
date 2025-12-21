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
    pub open spec fn flush_byte(self) -> u8 {
        match self.outstanding_write {
            None => self.state_at_last_flush,
            Some(b) => b,
        }
    }
}

pub struct PersistentMemoryRegionView {
    pub state: Seq<PersistentMemoryByte>,
}

impl PersistentMemoryRegionView {
    pub open spec fn len(self) -> nat {
        self.state.len()
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

pub struct PersistentMemoryConstants {
    pub impervious_to_corruption: bool,
}

pub trait PersistentMemoryRegion: Sized {

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

pub open spec fn memories_differ_only_where_subregion_allows(
    mem1: Seq<u8>,
    mem2: Seq<u8>,
    start: nat,
    len: nat,
    is_writable_absolute_addr_fn: spec_fn(int) -> bool,
) -> bool
    recommends
        0 <= start,
        0 <= len,
        mem1.len() == mem2.len(),
        start + len <= mem1.len(),
{
    forall|addr: int|
        {
            ||| 0 <= addr < start
            ||| start + len <= addr < mem1.len()
            ||| start <= addr < start + len && !is_writable_absolute_addr_fn(addr)
        } ==> mem1[addr] == #[trigger] mem2[addr]
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

pub open spec fn condition_sufficient_to_create_wrpm_subregion<Perm>(
    region_view: PersistentMemoryRegionView,
    perm: &Perm,
    start: u64,
    len: nat,
    is_writable_absolute_addr_fn: spec_fn(int) -> bool,
    condition: spec_fn(Seq<u8>) -> bool,
) -> bool where Perm: CheckPermission<Seq<u8>> {
    &&& 0 <= len
    &&& start + len <= region_view.len() <= u64::MAX
    &&& forall|crash_state| region_view.can_crash_as(crash_state) ==> condition(crash_state)
    &&& forall|crash_state| condition(crash_state) ==> perm.check_permission(crash_state)
    &&& forall|s1: Seq<u8>, s2: Seq<u8>|
        {
            &&& condition(s1)
            &&& s1.len() == s2.len() == region_view.len()
            &&& #[trigger] memories_differ_only_where_subregion_allows(
                s1,
                s2,
                start as nat,
                len,
                is_writable_absolute_addr_fn,
            )
        } ==> condition(s2)
}

#[verifier::external_body]
pub proof fn lemma_condition_sufficient_to_create_wrpm_subregion<Perm>(
    region_view: PersistentMemoryRegionView,
    perm: &Perm,
    start: u64,
    len: nat,
    is_writable_absolute_addr_fn: spec_fn(int) -> bool,
    condition: spec_fn(Seq<u8>) -> bool,
) where Perm: CheckPermission<Seq<u8>>
    requires
        condition_sufficient_to_create_wrpm_subregion(
            region_view,
            perm,
            start,
            len,
            is_writable_absolute_addr_fn,
            condition,
        ),
    ensures
        forall|alt_region_view: PersistentMemoryRegionView, alt_crash_state: Seq<u8>|
            {
                &&& #[trigger] alt_region_view.can_crash_as(alt_crash_state)
                &&& region_view.len() == alt_region_view.len()
                &&& views_differ_only_where_subregion_allows(
                    region_view,
                    alt_region_view,
                    start as nat,
                    len,
                    is_writable_absolute_addr_fn,
                )
            } ==> perm.check_permission(alt_crash_state),
{
    unimplemented!()
}

pub struct WriteRestrictedPersistentMemorySubregion {
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

    pub closed spec fn view<Perm, PMRegion>(
        self,
        wrpm: &WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
    ) -> PersistentMemoryRegionView where
        Perm: CheckPermission<Seq<u8>>,
        PMRegion: PersistentMemoryRegion,
     {
        get_subregion_view(wrpm@, self.start(), self.len())
    }

    pub closed spec fn opaque_inv<Perm, PMRegion>(
        self,
        wrpm: &WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        perm: &Perm,
    ) -> bool where Perm: CheckPermission<Seq<u8>>, PMRegion: PersistentMemoryRegion {
        &&& wrpm.inv()
        &&& wrpm.constants() == self.constants()
        &&& wrpm@.len() == self.initial_region_view().len()
        &&& self.initial_region_view().len() <= u64::MAX
        &&& self.start() + self.len() <= wrpm@.len()
        &&& self.view(wrpm).len() == self.len()
        &&& views_differ_only_where_subregion_allows(
            self.initial_region_view(),
            wrpm@,
            self.start(),
            self.len(),
            self.is_writable_absolute_addr_fn(),
        )
        &&& forall|alt_region_view: PersistentMemoryRegionView, alt_crash_state: Seq<u8>|
            {
                &&& #[trigger] alt_region_view.can_crash_as(alt_crash_state)
                &&& self.initial_region_view().len() == alt_region_view.len()
                &&& views_differ_only_where_subregion_allows(
                    self.initial_region_view(),
                    alt_region_view,
                    self.start(),
                    self.len(),
                    self.is_writable_absolute_addr_fn(),
                )
            } ==> perm.check_permission(alt_crash_state)
    }

    pub open spec fn inv<Perm, PMRegion>(
        self,
        wrpm: &WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        perm: &Perm,
    ) -> bool where Perm: CheckPermission<Seq<u8>>, PMRegion: PersistentMemoryRegion {
        &&& self.view(wrpm).len() == self.len()
        &&& self.opaque_inv(wrpm, perm)
    }

    #[verifier::auto_ext_equal(assert, assert_by, ensures)]
    pub exec fn new_with_condition<Perm, PMRegion>(
        wrpm: &WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        Tracked(perm): Tracked<&Perm>,
        start: u64,
        Ghost(len): Ghost<nat>,
        Ghost(is_writable_absolute_addr_fn): Ghost<spec_fn(int) -> bool>,
        Ghost(condition): Ghost<spec_fn(Seq<u8>) -> bool>,
    ) -> (result: Self) where Perm: CheckPermission<Seq<u8>>, PMRegion: PersistentMemoryRegion
        requires
            wrpm.inv(),
            condition_sufficient_to_create_wrpm_subregion(
                wrpm@,
                perm,
                start,
                len,
                is_writable_absolute_addr_fn,
                condition,
            ),
        ensures
            result.inv(wrpm, perm),
            result.constants() == wrpm.constants(),
            result.start() == start,
            result.len() == len,
            result.initial_region_view() == wrpm@,
            result.is_writable_absolute_addr_fn() == is_writable_absolute_addr_fn,
            result.view(wrpm) == result.initial_subregion_view(),
            result.view(wrpm) == get_subregion_view(wrpm@, start as nat, len),
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

pub trait CheckPermission<State> {
    spec fn check_permission(&self, state: State) -> bool;
}

pub struct WriteRestrictedPersistentMemoryRegion<Perm, PMRegion> where
    Perm: CheckPermission<Seq<u8>>,
    PMRegion: PersistentMemoryRegion,
 {
    pm_region: PMRegion,
    ghost perm: Option<Perm>,
}

impl<Perm, PMRegion> WriteRestrictedPersistentMemoryRegion<Perm, PMRegion> where
    Perm: CheckPermission<Seq<u8>>,
    PMRegion: PersistentMemoryRegion,
 {
    pub closed spec fn view(&self) -> PersistentMemoryRegionView;

    pub closed spec fn inv(&self) -> bool;

    pub closed spec fn constants(&self) -> PersistentMemoryConstants;
}

pub fn main() {
}

} // verus!
