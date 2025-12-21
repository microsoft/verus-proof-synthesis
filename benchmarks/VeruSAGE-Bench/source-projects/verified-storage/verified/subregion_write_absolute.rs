use vstd::prelude::*;

verus! {

pub fn main() {
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

/*pmem\wrpm_t*/

pub trait CheckPermission<State> {
    spec fn check_permission(&self, state: State) -> bool;
}

pub struct WriteRestrictedPersistentMemoryRegion<Perm, PMRegion> where
    Perm: CheckPermission<Seq<u8>>,
    PMRegion: PersistentMemoryRegion,
 {
    pm_region: PMRegion,
    ghost perm: Option<
        Perm,
    >,  // Needed to work around Rust limitation that Perm must be referenced
}

impl<Perm, PMRegion> WriteRestrictedPersistentMemoryRegion<Perm, PMRegion> where
    Perm: CheckPermission<Seq<u8>>,
    PMRegion: PersistentMemoryRegion,
 {
    #[verifier::external_body]
    pub closed spec fn view(&self) -> PersistentMemoryRegionView {
        unimplemented!()
    }

    #[verifier::external_body]
    pub closed spec fn inv(&self) -> bool {
        unimplemented!()
    }

    #[verifier::external_body]
    pub closed spec fn constants(&self) -> PersistentMemoryConstants {
        unimplemented!()
    }

    #[verifier::external_body]
    pub exec fn write(&mut self, addr: u64, bytes: &[u8], perm: Tracked<&Perm>)
        requires
            old(self).inv(),
            addr + bytes@.len() <= old(self)@.len(),
            addr + bytes@.len() <= u64::MAX,
            old(self)@.no_outstanding_writes_in_range(addr as int, addr + bytes@.len()),
            // The key thing the caller must prove is that all crash states are authorized by `perm`
            forall|s|
                old(self)@.write(addr as int, bytes@).can_crash_as(s)
                    ==> #[trigger] perm@.check_permission(s),
        ensures
            self.inv(),
            self.constants() == old(self).constants(),
            self@ == old(self)@.write(addr as int, bytes@),
    {
        unimplemented!()
    }
}

/*pmem\pmemspec_t*/

pub open spec fn const_persistence_chunk_size() -> int {
    8
}

#[verifier::ext_equal]
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

#[verifier::ext_equal]
pub struct PersistentMemoryConstants {
    pub impervious_to_corruption: bool,
}

pub trait PersistentMemoryRegion: Sized {

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

    pub exec fn write_absolute<Perm, PMRegion>(
        self: &Self,
        wrpm: &mut WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        absolute_addr: u64,
        bytes: &[u8],
        Tracked(perm): Tracked<&Perm>,
    ) where Perm: CheckPermission<Seq<u8>>, PMRegion: PersistentMemoryRegion
        requires
            self.inv(old(wrpm), perm),
            self.start() <= absolute_addr,
            absolute_addr + bytes@.len() <= self.len(),
            self.view(old(wrpm)).no_outstanding_writes_in_range(
                absolute_addr - self.start(),
                absolute_addr + bytes@.len() - self.start(),
            ),
            forall|i: int|
                absolute_addr <= i < absolute_addr + bytes@.len()
                    ==> #[trigger] self.is_writable_absolute_addr_fn()(i),
        ensures
            self.inv(wrpm, perm),
            self.view(wrpm) == self.view(old(wrpm)).write(absolute_addr - self.start(), bytes@),
    {
        let ghost subregion_view = self.view(wrpm).write(absolute_addr - self.start(), bytes@);
        assert forall|i|
            #![trigger wrpm@.state[i]]
            absolute_addr <= i < absolute_addr
                + bytes@.len() implies wrpm@.state[i].outstanding_write.is_none() by {
            assert(wrpm@.state[i] == self.view(wrpm).state[i - self.start()]);
        }
        wrpm.write(absolute_addr, bytes, Tracked(perm));
        assert(self.view(wrpm) =~= subregion_view);
    }
}

} // verus!
