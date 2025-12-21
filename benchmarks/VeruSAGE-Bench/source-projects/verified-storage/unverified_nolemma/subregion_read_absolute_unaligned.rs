use deps_hack::pmsized_primitive;
use vstd::prelude::*;
verus! {

#[verifier::external_body]
pub proof fn axiom_bytes_len<S: PmCopy>(s: S)
    ensures
        #[trigger] s.spec_to_bytes().len() == S::spec_size_of(),
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn axiom_to_from_bytes<S: PmCopy>(s: S)
    ensures
        s == #[trigger] S::spec_from_bytes(s.spec_to_bytes()),
{
    unimplemented!()
}

pub trait PmCopy: PmSized + SpecPmSized + Sized + Copy {

}

pub trait PmCopyHelper: PmCopy {
    spec fn spec_to_bytes(self) -> Seq<u8>;

    spec fn spec_from_bytes(bytes: Seq<u8>) -> Self;
}

impl<T> PmCopyHelper for T where T: PmCopy {
    closed spec fn spec_to_bytes(self) -> Seq<u8>;

    closed spec fn spec_from_bytes(bytes: Seq<u8>) -> Self;
}

impl PmCopy for u64 {

}

global size_of usize == 8;

global size_of isize == 8;

pub trait SpecPmSized: UnsafeSpecPmSized {
    spec fn spec_size_of() -> nat;

    spec fn spec_align_of() -> nat;
}

pmsized_primitive!(u8);

pmsized_primitive!(u64);

pmsized_primitive!(usize);

pmsized_primitive!(isize);

pmsized_primitive!(bool);

impl<T: PmSized, const N: usize> SpecPmSized for [T; N] {
    open spec fn spec_size_of() -> nat {
        (N * T::spec_size_of()) as nat
    }

    open spec fn spec_align_of() -> nat {
        T::spec_align_of()
    }
}

pub enum PmemError {
    InvalidFileName,
    CannotOpenPmFile,
    NotPm,
    PmdkError,
    AccessOutOfRange,
}

pub closed spec fn maybe_corrupted_byte(byte: u8, true_byte: u8, addr: int) -> bool;

pub open spec fn maybe_corrupted(bytes: Seq<u8>, true_bytes: Seq<u8>, addrs: Seq<int>) -> bool {
    &&& bytes.len() == true_bytes.len() == addrs.len()
    &&& forall|i: int|
        #![auto]
        0 <= i < bytes.len() ==> maybe_corrupted_byte(bytes[i], true_bytes[i], addrs[i])
}

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

    pub open spec fn no_outstanding_writes_in_range(self, i: int, j: int) -> bool {
        forall|k| i <= k < j ==> (#[trigger] self.state[k].outstanding_write).is_none()
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

pub struct PersistentMemoryConstants {
    pub impervious_to_corruption: bool,
}

pub trait PersistentMemoryRegion: Sized {
    spec fn view(&self) -> PersistentMemoryRegionView;

    spec fn inv(&self) -> bool;

    spec fn constants(&self) -> PersistentMemoryConstants;

    fn read_unaligned(&self, addr: u64, num_bytes: u64) -> (bytes: Result<Vec<u8>, PmemError>)
        requires
            self.inv(),
            addr + num_bytes <= self@.len(),
            self@.no_outstanding_writes_in_range(addr as int, addr + num_bytes),
        ensures
            match bytes {
                Ok(bytes) => {
                    let true_bytes = self@.committed().subrange(addr as int, addr + num_bytes);
                    let addrs = Seq::<int>::new(num_bytes as nat, |i: int| i + addr);
                    &&& if self.constants().impervious_to_corruption {
                        bytes@ == true_bytes
                    } else {
                        maybe_corrupted(bytes@, true_bytes, addrs)
                    }
                },
                _ => false,
            },
    ;
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

    pub open spec fn end(self) -> nat {
        self.start() + self.len()
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

    #[verifier::auto_ext_equal(assert, assert_by, ensures)]
    pub exec fn read_absolute_unaligned<Perm, PMRegion>(
        self: &Self,
        wrpm: &WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        absolute_addr: u64,
        num_bytes: u64,
        Tracked(perm): Tracked<&Perm>,
    ) -> (result: Result<Vec<u8>, PmemError>) where
        Perm: CheckPermission<Seq<u8>>,
        PMRegion: PersistentMemoryRegion,

        requires
            self.inv(wrpm, perm),
            self.start() <= absolute_addr,
            absolute_addr + num_bytes <= self.end(),
            self.view(wrpm).no_outstanding_writes_in_range(
                absolute_addr - self.start(),
                absolute_addr + num_bytes - self.start(),
            ),
        ensures
            match result {
                Ok(bytes) => {
                    let true_bytes = self.view(wrpm).committed().subrange(
                        absolute_addr - self.start(),
                        absolute_addr + num_bytes - self.start(),
                    );
                    if wrpm.constants().impervious_to_corruption {
                        bytes@ == true_bytes
                    } else {
                        let absolute_addrs = Seq::<int>::new(
                            num_bytes as nat,
                            |i: int| absolute_addr + i,
                        );
                        maybe_corrupted(bytes@, true_bytes, absolute_addrs)
                    }
                },
                Err(e) => e == PmemError::AccessOutOfRange,
            },
    {
        let ret = wrpm.get_pm_region_ref().read_unaligned(absolute_addr, num_bytes);
        ret
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

    #[verifier::external_body]
    pub exec fn get_pm_region_ref(&self) -> (pm_region: &PMRegion)
        requires
            self.inv(),
        ensures
            pm_region.inv(),
            pm_region@ == self@,
            pm_region.constants() == self.constants(),
    {
        unimplemented!()
    }
}

#[verifier::external_trait_specification]
pub trait ExPmSized: SpecPmSized {
    type ExternalTraitSpecificationFor: PmSized;

    fn size_of() -> (out: usize)
        ensures
            out as int == Self::spec_size_of(),
    ;

    fn align_of() -> (out: usize)
        ensures
            out as int == Self::spec_align_of(),
    ;
}

#[verifier::external_trait_specification]
pub trait ExUnsafeSpecPmSized {
    type ExternalTraitSpecificationFor: UnsafeSpecPmSized;
}

pub fn main() {
}

pub fn size_of<S: PmSized>() -> (out: usize)
    ensures
        out as nat == S::spec_size_of(),
{
    S::size_of()
}

pub fn align_of<S: PmSized>() -> (out: usize)
    ensures
        out as nat == S::spec_align_of(),
{
    S::align_of()
}

} // verus!
pub unsafe trait PmSized: SpecPmSized {
    fn size_of() -> usize;
    fn align_of() -> usize;
}
pub unsafe trait ConstPmSized {
    const SIZE: usize;
    const ALIGN: usize;
}
pub unsafe trait UnsafeSpecPmSized {}
unsafe impl<T: PmSized, const N: usize> PmSized for [T; N] {
    fn size_of() -> usize {
        N * T::size_of()
    }
    fn align_of() -> usize {
        T::align_of()
    }
}
unsafe impl<T: PmSized, const N: usize> UnsafeSpecPmSized for [T; N] {}
unsafe impl<T: PmSized + ConstPmSized, const N: usize> ConstPmSized for [T; N] {
    const SIZE: usize = N * T::SIZE;
    const ALIGN: usize = T::ALIGN;
}
