use deps_hack::{pmsized_primitive, PmSized};
use vstd::prelude::*;

// The unsafe trait PmSized provides non-const exec methods that return the size and alignment
// of a type as calculated by the PmSize derive macro. This trait is visible to Verus via
// an external trait specification, which axiomatizes that the size and alignment given by these
// methods match that which is given by the spec functions. Due to limitations in Verus and Rust,
// we can't make implementations of this trait or its methods constant. We use the trait
// ConstPmSized below, which is not visible to Verus, to obtain constant size and alignment values,
// which are checked at compile time and should be returned by the methods of this trait.
//
// Ideally, this would be a constant trait defined within Verus, with verified methods. This is
// not currently possible due to limitations in Verus, so we have to use this workaround.
pub unsafe trait PmSized: SpecPmSized {
    fn size_of() -> usize;
    fn align_of() -> usize;
}

// ConstPmSized's associated constants store the size and alignment of an implementing
// type as calculated by the PmSized derive macro. This trait is not visible to Verus,
// since Verus does not currently support associated constants. The size_of and align_of
// methods in PmSized, which ARE visible to Verus but are external-body, return
// these associated constants.
pub unsafe trait ConstPmSized {
    const SIZE: usize;
    const ALIGN: usize;
}

// This unsafe marker trait is a supertrait of SpecPmSized to ensure that
// types cannot safely provide their own implementations of SpecPmSized.
// This is a workaround for the fact that Verus does not support unsafe traits;
// only externally-defined traits can be unsafe.
pub unsafe trait UnsafeSpecPmSized {}

// Arrays are PmSized, but since the implementation is generic
// we provide a manual implementation here rather than using the pmsized_primitive!
// macro. These traits are unsafe and must be implemented outside of verus!.
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
verus! {

pub fn main() {
}

/*log\logspec_t*/

pub struct AbstractLogState {
    pub head: int,
    pub log: Seq<u8>,
    pub pending: Seq<u8>,
    pub capacity: int,
}

impl AbstractLogState {
    pub open spec fn drop_pending_appends(self) -> Self {
        Self { pending: Seq::<u8>::empty(), ..self }
    }
}

/*util_v*/

pub open spec fn nat_seq_max(seq: Seq<nat>) -> nat
    recommends
        0 < seq.len(),
    decreases seq.len(),
{
    if seq.len() == 1 {
        seq[0]
    } else if seq.len() == 0 {
        0
    } else {
        let later_max = nat_seq_max(seq.drop_first());
        if seq[0] >= later_max {
            seq[0]
        } else {
            later_max
        }
    }
}

/*pmem\pmcopy_t*/

pub broadcast group pmcopy_axioms {
    axiom_bytes_len,
    axiom_to_from_bytes,
}

pub trait PmCopy: PmSized + SpecPmSized + Sized + Copy {

}

// PmCopyHelper is a subtrait of PmCopy that exists to provide a blanket
// implementation of these methods for all PmCopy objects.
pub trait PmCopyHelper: PmCopy {
    spec fn spec_to_bytes(self) -> Seq<u8>;

    spec fn spec_from_bytes(bytes: Seq<u8>) -> Self;

    spec fn bytes_parseable(bytes: Seq<u8>) -> bool;

    spec fn spec_crc(self) -> u64;
}

impl<T> PmCopyHelper for T where T: PmCopy {
    closed spec fn spec_to_bytes(self) -> Seq<u8>;

    #[verifier::external_body]
    closed spec fn spec_from_bytes(bytes: Seq<u8>) -> Self {
        unimplemented!()
    }

    open spec fn spec_crc(self) -> u64 {
        spec_crc_u64(self.spec_to_bytes())
    }

    open spec fn bytes_parseable(bytes: Seq<u8>) -> bool {
        Self::spec_from_bytes(bytes).spec_to_bytes() == bytes
    }
}

#[verifier::external_body]
pub broadcast proof fn axiom_bytes_len<S: PmCopy>(s: S)
    ensures
        #[trigger] s.spec_to_bytes().len() == S::spec_size_of(),
{
    unimplemented!()
}

#[verifier::external_body]
pub broadcast proof fn axiom_to_from_bytes<S: PmCopy>(s: S)
    ensures
        s == #[trigger] S::spec_from_bytes(s.spec_to_bytes()),
{
    unimplemented!()
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

pmsized_primitive!(u128);

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

#[verifier::opaque]
pub open spec fn spec_padding_needed(offset: nat, align: nat) -> nat {
    let misalignment = offset % align;
    if misalignment > 0 {
        // we can safely cast this to a nat because it will always be the case that
        // misalignment <= align
        (align - misalignment) as nat
    } else {
        0
    }
}

pub const fn padding_needed(offset: usize, align: usize) -> (out: usize)
    requires
        align > 0,
    ensures
        out <= align,
        out as nat == spec_padding_needed(offset as nat, align as nat),
{
    reveal(spec_padding_needed);
    let misalignment = offset % align;
    if misalignment > 0 {
        align - misalignment
    } else {
        0
    }
}

/*pmem\pmemspec_t*/

pub closed spec fn spec_crc_u64(bytes: Seq<u8>) -> u64;

pub const CDB_FALSE: u64 = 0xa32842d19001605e;

// CRC(b"0")
pub const CDB_TRUE: u64 = 0xab21aa73069531b7;

// CRC(b"1")
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

pub struct PersistentMemoryConstants {
    pub impervious_to_corruption: bool,
}

pub trait PersistentMemoryRegion: Sized {

}

pub open spec fn extract_bytes(bytes: Seq<u8>, pos: nat, len: nat) -> Seq<u8> {
    bytes.subrange(pos as int, (pos + len) as int)
}

/*pmem\pmemutil_v*/

#[verifier::external_body]
pub proof fn lemma_single_write_crash_effect_on_pm_region_view(
    pm_region_view: PersistentMemoryRegionView,
    write_addr: int,
    bytes_to_write: Seq<u8>,
)
    requires
        bytes_to_write.len() == const_persistence_chunk_size(),
        write_addr % const_persistence_chunk_size() == 0,
        0 <= write_addr,
        write_addr + const_persistence_chunk_size() <= pm_region_view.len(),
        pm_region_view.no_outstanding_writes(),
    ensures
        ({
            let new_pm_region_view = pm_region_view.write(write_addr, bytes_to_write);
            forall|crash_bytes: Seq<u8>|
                new_pm_region_view.can_crash_as(crash_bytes) ==> {
                    ||| crash_bytes == pm_region_view.committed()
                    ||| crash_bytes == new_pm_region_view.flush().committed()
                }
        }),
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn lemma_write_reflected_after_flush_committed(
    pm_region_view: PersistentMemoryRegionView,
    addr: int,
    bytes: Seq<u8>,
)
    requires
        0 <= addr,
        addr + bytes.len() <= pm_region_view.len(),
    ensures
        pm_region_view.write(addr, bytes).flush().committed().subrange(
            addr as int,
            addr + bytes.len(),
        ) == bytes,
{
    unimplemented!()
}

/*pmem\wrpm_t*/

pub trait CheckPermission<State> {
    spec fn check_permission(&self, state: State) -> bool;
}

#[allow(dead_code)]
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
    pub exec fn serialize_and_write<S>(
        &mut self,
        addr: u64,
        to_write: &S,
        perm: Tracked<&Perm>,
    ) where S: PmCopy + Sized
        requires
            old(self).inv(),
            addr + S::spec_size_of() <= old(self)@.len(),
            old(self)@.no_outstanding_writes_in_range(addr as int, addr + S::spec_size_of()),
            // The key thing the caller must prove is that all crash states are authorized by `perm`
            forall|s|
                old(self)@.write(addr as int, to_write.spec_to_bytes()).can_crash_as(s)
                    ==> #[trigger] perm@.check_permission(s),
        ensures
            self.inv(),
            self.constants() == old(self).constants(),
            self@ == old(self)@.write(addr as int, to_write.spec_to_bytes()),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub exec fn flush(&mut self)
        requires
            old(self).inv(),
        ensures
            self.inv(),
            self@ == old(self)@.flush(),
            self.constants() == old(self).constants(),
    {
        unimplemented!()
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

pub struct WriteRestrictedPersistentMemorySubregion {
    start_: u64,
    len_: Ghost<nat>,
    constants_: Ghost<PersistentMemoryConstants>,
    initial_region_view_: Ghost<PersistentMemoryRegionView>,
    is_writable_absolute_addr_fn_: Ghost<spec_fn(int) -> bool>,
}

impl WriteRestrictedPersistentMemorySubregion {
    #[verifier::external_body]
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
        unimplemented!()
    }

    #[verifier::external_body]
    pub closed spec fn constants(self) -> PersistentMemoryConstants {
        unimplemented!()
    }

    #[verifier::external_body]
    pub closed spec fn start(self) -> nat {
        unimplemented!()
    }

    #[verifier::external_body]
    pub closed spec fn len(self) -> nat {
        unimplemented!()
    }

    #[verifier::external_body]
    pub closed spec fn initial_region_view(self) -> PersistentMemoryRegionView {
        unimplemented!()
    }

    #[verifier::external_body]
    pub closed spec fn is_writable_absolute_addr_fn(self) -> spec_fn(int) -> bool {
        unimplemented!()
    }

    #[verifier::external_body]
    pub closed spec fn initial_subregion_view(self) -> PersistentMemoryRegionView {
        unimplemented!()
    }

    #[verifier::external_body]
    pub closed spec fn view<Perm, PMRegion>(
        self,
        wrpm: &WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
    ) -> PersistentMemoryRegionView where
        Perm: CheckPermission<Seq<u8>>,
        PMRegion: PersistentMemoryRegion,
     {
        unimplemented!()
    }

    #[verifier::external_body]
    pub closed spec fn opaque_inv<Perm, PMRegion>(
        self,
        wrpm: &WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        perm: &Perm,
    ) -> bool where Perm: CheckPermission<Seq<u8>>, PMRegion: PersistentMemoryRegion {
        unimplemented!()
    }

    pub open spec fn inv<Perm, PMRegion>(
        self,
        wrpm: &WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        perm: &Perm,
    ) -> bool where Perm: CheckPermission<Seq<u8>>, PMRegion: PersistentMemoryRegion {
        &&& self.view(wrpm).len() == self.len()
        &&& self.opaque_inv(wrpm, perm)
    }

    #[verifier::external_body]
    pub proof fn lemma_reveal_opaque_inv<Perm, PMRegion>(
        self,
        wrpm: &WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        perm: &Perm,
    ) where Perm: CheckPermission<Seq<u8>>, PMRegion: PersistentMemoryRegion
        requires
            self.inv(wrpm, perm),
        ensures
            wrpm.inv(),
            wrpm.constants() == self.constants(),
            wrpm@.len() == self.initial_region_view().len(),
            views_differ_only_where_subregion_allows(
                self.initial_region_view(),
                wrpm@,
                self.start(),
                self.len(),
                self.is_writable_absolute_addr_fn(),
            ),
            self.view(wrpm) == get_subregion_view(wrpm@, self.start(), self.len()),
            forall|addr: int|
                0 <= addr < self.len() ==> #[trigger] self.view(wrpm).state[addr]
                    == wrpm@.state[addr + self.start()],
    {
        unimplemented!()
    }
}

/*pmem\traits_t*/

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

// The specifications of these methods in ExPmSized are
// not useable in verified code; use these verified wrappers
// instead to obtain the runtime size and alignment of a type.
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

/*log\inv_v*/

pub open spec fn no_outstanding_writes_to_metadata(
    pm_region_view: PersistentMemoryRegionView,
) -> bool {
    pm_region_view.no_outstanding_writes_in_range(
        ABSOLUTE_POS_OF_GLOBAL_METADATA as int,
        ABSOLUTE_POS_OF_LOG_AREA as int,
    )
}

pub open spec fn inactive_metadata_types_set(mem: Seq<u8>) -> bool {
    let cdb_pos = ABSOLUTE_POS_OF_LOG_CDB as int;
    let cdb = u64::spec_from_bytes(mem.subrange(cdb_pos, cdb_pos + u64::spec_size_of()));
    let metadata_pos = if cdb == CDB_TRUE {
        ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as int
    } else {
        ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_TRUE as int
    };
    let metadata = LogMetadata::spec_from_bytes(
        mem.subrange(metadata_pos, metadata_pos + LogMetadata::spec_size_of()),
    );
    let crc_pos = if cdb == CDB_TRUE {
        ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_FALSE as int
    } else {
        ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_TRUE as int
    };
    let crc = u64::spec_from_bytes(mem.subrange(crc_pos, crc_pos + u64::spec_size_of()));
    &&& u64::bytes_parseable(mem.subrange(cdb_pos, cdb_pos + u64::spec_size_of()))
    &&& LogMetadata::bytes_parseable(
        mem.subrange(metadata_pos, metadata_pos + LogMetadata::spec_size_of()),
    )
    &&& u64::bytes_parseable(mem.subrange(crc_pos, crc_pos + u64::spec_size_of()))
    &&& cdb == CDB_TRUE || cdb == CDB_FALSE
    &&& crc == spec_crc_u64(metadata.spec_to_bytes())
}

pub open spec fn memory_matches_deserialized_cdb(
    pm_region_view: PersistentMemoryRegionView,
    cdb: bool,
) -> bool {
    &&& pm_region_view.no_outstanding_writes_in_range(
        ABSOLUTE_POS_OF_LOG_CDB as int,
        ABSOLUTE_POS_OF_LOG_CDB + u64::spec_size_of(),
    )
    &&& deserialize_and_check_log_cdb(pm_region_view.committed()) == Some(cdb)
}

pub open spec fn metadata_consistent_with_info(
    pm_region_view: PersistentMemoryRegionView,
    log_id: u128,
    cdb: bool,
    info: LogInfo,
) -> bool {
    let mem = pm_region_view.committed();
    let global_metadata = deserialize_global_metadata(mem);
    let global_crc = deserialize_global_crc(mem);
    let region_metadata = deserialize_region_metadata(mem);
    let region_crc = deserialize_region_crc(mem);
    let log_metadata = deserialize_log_metadata(mem, cdb);
    let log_crc = deserialize_log_crc(mem, cdb);

    // No outstanding writes to global metadata, region metadata, or the log metadata CDB
    &&& pm_region_view.no_outstanding_writes_in_range(
        ABSOLUTE_POS_OF_GLOBAL_METADATA as int,
        ABSOLUTE_POS_OF_LOG_CDB as int,
    )
    // Also, no outstanding writes to the log metadata corresponding to the active log metadata CDB
    &&& pm_region_view.no_outstanding_writes_in_range(
        get_log_metadata_pos(cdb) as int,
        get_log_crc_end(cdb) as int,
    )
    // All the CRCs match
    &&& global_crc == global_metadata.spec_crc()
    &&& region_crc == region_metadata.spec_crc()
    &&& log_crc
        == log_metadata.spec_crc()
    // Various fields are valid and match the parameters to this function
    &&& global_metadata.program_guid == LOG_PROGRAM_GUID
    &&& global_metadata.version_number == LOG_PROGRAM_VERSION_NUMBER
    &&& global_metadata.length_of_region_metadata == RegionMetadata::spec_size_of()
    &&& region_metadata.region_size == mem.len()
    &&& region_metadata.log_id == log_id
    &&& region_metadata.log_area_len == info.log_area_len
    &&& log_metadata.head == info.head
    &&& log_metadata.log_length
        == info.log_length
    // The memory region is large enough to hold the entirety of the log area
    &&& mem.len() >= ABSOLUTE_POS_OF_LOG_AREA + info.log_area_len
}

#[verifier::external_body]
pub proof fn lemma_metadata_consistent_with_info_after_cdb_update(
    old_pm_region_view: PersistentMemoryRegionView,
    new_pm_region_view: PersistentMemoryRegionView,
    log_id: u128,
    new_cdb_bytes: Seq<u8>,
    new_cdb: bool,
    info: LogInfo,
)
    requires
        new_cdb == false ==> new_cdb_bytes == CDB_FALSE.spec_to_bytes(),
        new_cdb == true ==> new_cdb_bytes == CDB_TRUE.spec_to_bytes(),
        new_cdb_bytes.len() == u64::spec_size_of(),
        old_pm_region_view.no_outstanding_writes(),
        new_pm_region_view.no_outstanding_writes(),
        new_pm_region_view =~= old_pm_region_view.write(
            ABSOLUTE_POS_OF_LOG_CDB as int,
            new_cdb_bytes,
        ).flush(),
        metadata_consistent_with_info(old_pm_region_view, log_id, new_cdb, info),
    ensures
        metadata_consistent_with_info(new_pm_region_view, log_id, new_cdb, info),
{
    unimplemented!()
}

pub open spec fn info_consistent_with_log_area(
    log_area_view: PersistentMemoryRegionView,
    info: LogInfo,
    state: AbstractLogState,
) -> bool {
    // `info` satisfies certain invariant properties
    &&& info.log_area_len >= MIN_LOG_AREA_SIZE
    &&& info.log_length <= info.log_plus_pending_length <= info.log_area_len
    &&& info.head_log_area_offset == info.head as int % info.log_area_len as int
    &&& info.head + info.log_plus_pending_length
        <= u128::MAX
    // `info` and `state` are consistent with each other
    &&& state.log.len() == info.log_length
    &&& state.pending.len() == info.log_plus_pending_length - info.log_length
    &&& state.head == info.head
    &&& state.capacity
        == info.log_area_len
    // The log area is consistent with `info` and `state`
    &&& forall|pos_relative_to_head: int|
        {
            let log_area_offset = #[trigger] relative_log_pos_to_log_area_offset(
                pos_relative_to_head,
                info.head_log_area_offset as int,
                info.log_area_len as int,
            );
            let pmb = log_area_view.state[log_area_offset];
            &&& 0 <= pos_relative_to_head < info.log_length ==> {
                &&& pmb.state_at_last_flush == state.log[pos_relative_to_head]
                &&& pmb.outstanding_write.is_none()
            }
            &&& info.log_length <= pos_relative_to_head < info.log_plus_pending_length
                ==> pmb.flush_byte() == state.pending[pos_relative_to_head - info.log_length]
            &&& info.log_plus_pending_length <= pos_relative_to_head < info.log_area_len
                ==> pmb.outstanding_write.is_none()
        }
}

pub open spec fn info_consistent_with_log_area_in_region(
    pm_region_view: PersistentMemoryRegionView,
    info: LogInfo,
    state: AbstractLogState,
) -> bool {
    &&& pm_region_view.len() >= ABSOLUTE_POS_OF_LOG_AREA + info.log_area_len
    &&& info_consistent_with_log_area(
        get_subregion_view(
            pm_region_view,
            ABSOLUTE_POS_OF_LOG_AREA as nat,
            info.log_area_len as nat,
        ),
        info,
        state,
    )
}

pub open spec fn metadata_types_set(mem: Seq<u8>) -> bool {
    &&& {
        let metadata_pos = ABSOLUTE_POS_OF_GLOBAL_METADATA as int;
        let crc_pos = ABSOLUTE_POS_OF_GLOBAL_CRC as int;
        let metadata = GlobalMetadata::spec_from_bytes(
            extract_bytes(mem, metadata_pos as nat, GlobalMetadata::spec_size_of()),
        );
        let crc = u64::spec_from_bytes(extract_bytes(mem, crc_pos as nat, u64::spec_size_of()));
        &&& GlobalMetadata::bytes_parseable(
            extract_bytes(mem, metadata_pos as nat, GlobalMetadata::spec_size_of()),
        )
        &&& u64::bytes_parseable(extract_bytes(mem, crc_pos as nat, u64::spec_size_of()))
        &&& crc == spec_crc_u64(metadata.spec_to_bytes())
    }
    &&& {
        let metadata_pos = ABSOLUTE_POS_OF_REGION_METADATA as int;
        let crc_pos = ABSOLUTE_POS_OF_REGION_CRC as int;
        let metadata = RegionMetadata::spec_from_bytes(
            extract_bytes(mem, metadata_pos as nat, RegionMetadata::spec_size_of()),
        );
        let crc = u64::spec_from_bytes(extract_bytes(mem, crc_pos as nat, u64::spec_size_of()));
        &&& RegionMetadata::bytes_parseable(
            extract_bytes(mem, metadata_pos as nat, RegionMetadata::spec_size_of()),
        )
        &&& u64::bytes_parseable(extract_bytes(mem, crc_pos as nat, u64::spec_size_of()))
        &&& crc == spec_crc_u64(metadata.spec_to_bytes())
    }
    &&& {
        let cdb_pos = ABSOLUTE_POS_OF_LOG_CDB as int;
        let cdb = u64::spec_from_bytes(extract_bytes(mem, cdb_pos as nat, u64::spec_size_of()));
        let metadata_pos = if cdb == CDB_TRUE {
            ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_TRUE
        } else {
            ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE
        };
        let metadata = LogMetadata::spec_from_bytes(
            extract_bytes(mem, metadata_pos as nat, LogMetadata::spec_size_of()),
        );
        let crc_pos = if cdb == CDB_TRUE {
            ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_TRUE
        } else {
            ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_FALSE
        };
        let crc = u64::spec_from_bytes(extract_bytes(mem, crc_pos as nat, u64::spec_size_of()));
        &&& u64::bytes_parseable(extract_bytes(mem, cdb_pos as nat, u64::spec_size_of()))
        &&& cdb == CDB_TRUE || cdb == CDB_FALSE
        &&& LogMetadata::bytes_parseable(
            extract_bytes(mem, metadata_pos as nat, LogMetadata::spec_size_of()),
        )
        &&& u64::bytes_parseable(extract_bytes(mem, crc_pos as nat, u64::spec_size_of()))
        &&& crc == spec_crc_u64(metadata.spec_to_bytes())
    }
}

#[verifier::external_body]
pub proof fn lemma_invariants_imply_crash_recover_forall(
    pm_region_view: PersistentMemoryRegionView,
    log_id: u128,
    cdb: bool,
    info: LogInfo,
    state: AbstractLogState,
)
    requires
        memory_matches_deserialized_cdb(pm_region_view, cdb),
        metadata_consistent_with_info(pm_region_view, log_id, cdb, info),
        info_consistent_with_log_area_in_region(pm_region_view, info, state),
        metadata_types_set(pm_region_view.committed()),
    ensures
        forall|mem| #[trigger]
            pm_region_view.can_crash_as(mem) ==> {
                &&& recover_cdb(mem) == Some(cdb)
                &&& recover_state(mem, log_id) == Some(state.drop_pending_appends())
                &&& metadata_types_set(mem)
            },
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn lemma_flushing_metadata_maintains_invariants(
    pm_region_view: PersistentMemoryRegionView,
    log_id: u128,
    cdb: bool,
    info: LogInfo,
    state: AbstractLogState,
)
    requires
        memory_matches_deserialized_cdb(pm_region_view, cdb),
        metadata_consistent_with_info(pm_region_view, log_id, cdb, info),
        info_consistent_with_log_area_in_region(pm_region_view, info, state),
        metadata_types_set(pm_region_view.committed()),
    ensures
        ({
            let pm_region_view2 = pm_region_view.flush();
            &&& memory_matches_deserialized_cdb(pm_region_view2, cdb)
            &&& metadata_consistent_with_info(pm_region_view2, log_id, cdb, info)
            &&& info_consistent_with_log_area_in_region(pm_region_view2, info, state)
            &&& metadata_types_set(pm_region_view2.committed())
        }),
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn lemma_metadata_types_set_after_cdb_update(
    old_pm_region_view: PersistentMemoryRegionView,
    new_pm_region_view: PersistentMemoryRegionView,
    log_id: u128,
    new_cdb_bytes: Seq<u8>,
    old_cdb: bool,
)
    requires
        old_pm_region_view.no_outstanding_writes(),
        new_pm_region_view.no_outstanding_writes(),
        old_pm_region_view.len() >= ABSOLUTE_POS_OF_LOG_AREA,
        old_pm_region_view.len() == new_pm_region_view.len(),
        new_cdb_bytes == CDB_FALSE.spec_to_bytes() || new_cdb_bytes == CDB_TRUE.spec_to_bytes(),
        old_cdb ==> new_cdb_bytes == CDB_FALSE.spec_to_bytes(),
        !old_cdb ==> new_cdb_bytes == CDB_TRUE.spec_to_bytes(),
        new_pm_region_view =~= old_pm_region_view.write(
            ABSOLUTE_POS_OF_LOG_CDB as int,
            new_cdb_bytes,
        ).flush(),
        metadata_types_set(old_pm_region_view.committed()),
        inactive_metadata_types_set(old_pm_region_view.committed()),
    ensures
        metadata_types_set(new_pm_region_view.committed()),
{
    unimplemented!()
}

/*log\layout_v*/

pub const ABSOLUTE_POS_OF_GLOBAL_METADATA: u64 = 0;

pub const ABSOLUTE_POS_OF_GLOBAL_CRC: u64 = 32;

pub const ABSOLUTE_POS_OF_REGION_METADATA: u64 = 40;

pub const ABSOLUTE_POS_OF_REGION_CRC: u64 = 72;

pub const ABSOLUTE_POS_OF_LOG_CDB: u64 = 80;

pub const ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE: u64 = 88;

pub const ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_TRUE: u64 = 128;

pub const ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_FALSE: u64 = 120;

pub const ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_TRUE: u64 = 160;

pub const ABSOLUTE_POS_OF_LOG_AREA: u64 = 256;

pub const MIN_LOG_AREA_SIZE: u64 = 1;

pub const LOG_PROGRAM_GUID: u128 = 0x8eecd9dea2de4443903e2acf951380bf;

pub const LOG_PROGRAM_VERSION_NUMBER: u64 = 1;

#[repr(C)]
#[derive(PmSized, Copy, Clone, Default)]
pub struct GlobalMetadata {
    pub version_number: u64,
    pub length_of_region_metadata: u64,
    pub program_guid: u128,
}

impl PmCopy for GlobalMetadata {

}

#[repr(C)]
#[derive(PmSized, Copy, Clone, Default)]
pub struct RegionMetadata {
    pub region_size: u64,
    pub log_area_len: u64,
    pub log_id: u128,
}

impl PmCopy for RegionMetadata {

}

#[repr(C)]
#[derive(PmSized, Copy, Clone, Default)]
pub struct LogMetadata {
    pub log_length: u64,
    pub _padding: u64,
    pub head: u128,
}

impl PmCopy for LogMetadata {

}

pub open spec fn extract_global_metadata(mem: Seq<u8>) -> Seq<u8> {
    extract_bytes(
        mem,
        ABSOLUTE_POS_OF_GLOBAL_METADATA as nat,
        GlobalMetadata::spec_size_of() as nat,
    )
}

pub open spec fn deserialize_global_metadata(mem: Seq<u8>) -> GlobalMetadata {
    let bytes = extract_global_metadata(mem);
    GlobalMetadata::spec_from_bytes(bytes)
}

pub open spec fn extract_global_crc(mem: Seq<u8>) -> Seq<u8> {
    extract_bytes(mem, ABSOLUTE_POS_OF_GLOBAL_CRC as nat, u64::spec_size_of() as nat)
}

pub open spec fn deserialize_global_crc(mem: Seq<u8>) -> u64 {
    let bytes = extract_global_crc(mem);
    u64::spec_from_bytes(bytes)
}

pub open spec fn extract_region_metadata(mem: Seq<u8>) -> Seq<u8> {
    extract_bytes(
        mem,
        ABSOLUTE_POS_OF_REGION_METADATA as nat,
        RegionMetadata::spec_size_of() as nat,
    )
}

pub open spec fn deserialize_region_metadata(mem: Seq<u8>) -> RegionMetadata {
    let bytes = extract_region_metadata(mem);
    RegionMetadata::spec_from_bytes(bytes)
}

pub open spec fn extract_region_crc(mem: Seq<u8>) -> Seq<u8> {
    extract_bytes(mem, ABSOLUTE_POS_OF_REGION_CRC as nat, u64::spec_size_of() as nat)
}

pub open spec fn deserialize_region_crc(mem: Seq<u8>) -> u64 {
    let bytes = extract_region_crc(mem);
    u64::spec_from_bytes(bytes)
}

pub open spec fn extract_log_cdb(mem: Seq<u8>) -> Seq<u8> {
    extract_bytes(mem, ABSOLUTE_POS_OF_LOG_CDB as nat, u64::spec_size_of() as nat)
}

pub open spec fn deserialize_log_cdb(mem: Seq<u8>) -> u64 {
    let bytes = extract_log_cdb(mem);
    u64::spec_from_bytes(bytes)
}

pub open spec fn deserialize_and_check_log_cdb(mem: Seq<u8>) -> Option<bool> {
    let log_cdb = deserialize_log_cdb(mem);
    if log_cdb == CDB_FALSE {
        Some(false)
    } else if log_cdb == CDB_TRUE {
        Some(true)
    } else {
        None
    }
}

pub open spec fn get_log_metadata_pos(cdb: bool) -> u64 {
    if cdb {
        ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_TRUE
    } else {
        ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE
    }
}

pub open spec fn get_log_crc_end(cdb: bool) -> u64 {
    (get_log_metadata_pos(cdb) + LogMetadata::spec_size_of() + u64::spec_size_of()) as u64
}

pub open spec fn extract_log_metadata(mem: Seq<u8>, cdb: bool) -> Seq<u8> {
    let pos = get_log_metadata_pos(cdb);
    extract_bytes(mem, pos as nat, LogMetadata::spec_size_of() as nat)
}

pub open spec fn deserialize_log_metadata(mem: Seq<u8>, cdb: bool) -> LogMetadata {
    let bytes = extract_log_metadata(mem, cdb);
    LogMetadata::spec_from_bytes(bytes)
}

pub open spec fn extract_log_crc(mem: Seq<u8>, cdb: bool) -> Seq<u8> {
    let pos = if cdb {
        ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_TRUE
    } else {
        ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_FALSE
    };
    extract_bytes(mem, pos as nat, u64::spec_size_of() as nat)
}

pub open spec fn deserialize_log_crc(mem: Seq<u8>, cdb: bool) -> u64 {
    let bytes = extract_log_crc(mem, cdb);
    u64::spec_from_bytes(bytes)
}

pub open spec fn relative_log_pos_to_log_area_offset(
    pos_relative_to_head: int,
    head_log_area_offset: int,
    log_area_len: int,
) -> int {
    let log_area_offset = head_log_area_offset + pos_relative_to_head;
    if log_area_offset >= log_area_len {
        log_area_offset - log_area_len
    } else {
        log_area_offset
    }
}

pub open spec fn extract_log_from_log_area(log_area: Seq<u8>, head: int, log_length: int) -> Seq<
    u8,
> {
    let head_log_area_offset = head % (log_area.len() as int);
    Seq::<u8>::new(
        log_length as nat,
        |pos_relative_to_head: int|
            log_area[relative_log_pos_to_log_area_offset(
                pos_relative_to_head,
                head_log_area_offset,
                log_area.len() as int,
            )],
    )
}

pub open spec fn recover_log_from_log_area_given_metadata(
    log_area: Seq<u8>,
    head: int,
    log_length: int,
) -> Option<AbstractLogState> {
    if log_length > log_area.len() || head + log_length > u128::MAX {
        None
    } else {
        Some(
            AbstractLogState {
                head,
                log: extract_log_from_log_area(log_area, head, log_length),
                pending: Seq::<u8>::empty(),
                capacity: log_area.len() as int,
            },
        )
    }
}

pub open spec fn recover_log(mem: Seq<u8>, log_area_len: int, head: int, log_length: int) -> Option<
    AbstractLogState,
> {
    recover_log_from_log_area_given_metadata(
        extract_bytes(mem, ABSOLUTE_POS_OF_LOG_AREA as nat, log_area_len as nat),
        head,
        log_length,
    )
}

pub open spec fn recover_given_cdb(mem: Seq<u8>, log_id: u128, cdb: bool) -> Option<
    AbstractLogState,
> {
    if mem.len() < ABSOLUTE_POS_OF_LOG_AREA + MIN_LOG_AREA_SIZE {
        // To be valid, the memory's length has to be big enough to store at least
        // `MIN_LOG_AREA_SIZE` in the log area.
        None
    } else {
        let global_metadata = deserialize_global_metadata(mem);
        let global_crc = deserialize_global_crc(mem);
        if global_crc != global_metadata.spec_crc() {
            // To be valid, the global metadata CRC has to be a valid CRC of the global metadata
            // encoded as bytes.
            None
        } else {
            if global_metadata.program_guid != LOG_PROGRAM_GUID {
                // To be valid, the global metadata has to refer to this program's GUID.
                // Otherwise, it wasn't created by this program.
                None
            } else if global_metadata.version_number == 1 {
                // If this metadata was written by version #1 of this code, then this is how to
                // interpret it:
                if global_metadata.length_of_region_metadata != RegionMetadata::spec_size_of() {
                    // To be valid, the global metadata's encoding of the region metadata's
                    // length has to be what we expect. (This version of the code doesn't
                    // support any other length of region metadata.)
                    None
                } else {
                    let region_metadata = deserialize_region_metadata(mem);
                    let region_crc = deserialize_region_crc(mem);
                    if region_crc != region_metadata.spec_crc() {
                        // To be valid, the region metadata CRC has to be a valid CRC of the region
                        // metadata encoded as bytes.
                        None
                    } else {
                        // To be valid, the region metadata's region size has to match the size of the
                        // region given to us. Also, its metadata has to match what we expect
                        // from the list of regions given to us. Finally, there has to be
                        // sufficient room for the log area.
                        if {
                            ||| region_metadata.region_size != mem.len()
                            ||| region_metadata.log_id != log_id
                            ||| region_metadata.log_area_len < MIN_LOG_AREA_SIZE
                            ||| mem.len() < ABSOLUTE_POS_OF_LOG_AREA + region_metadata.log_area_len
                        } {
                            None
                        } else {
                            let log_metadata = deserialize_log_metadata(mem, cdb);
                            let log_crc = deserialize_log_crc(mem, cdb);
                            if log_crc != log_metadata.spec_crc() {
                                // To be valid, the log metadata CRC has to be a valid CRC of the
                                // log metadata encoded as bytes. (This only applies to the
                                // "active" log metadata, i.e., the log metadata
                                // corresponding to the current CDB.)
                                None
                            } else {
                                recover_log(
                                    mem,
                                    region_metadata.log_area_len as int,
                                    log_metadata.head as int,
                                    log_metadata.log_length as int,
                                )
                            }
                        }
                    }
                }
            } else {
                // This version of the code doesn't know how to parse metadata for any other
                // versions of this code besides 1. If we reach this point, we're presumably
                // reading metadata written by a future version of this code, which we can't
                // interpret.
                None
            }
        }
    }
}

pub open spec fn recover_cdb(mem: Seq<u8>) -> Option<bool> {
    if mem.len() < ABSOLUTE_POS_OF_REGION_METADATA {
        // If there isn't space in memory to store the global metadata
        // and CRC, then this region clearly isn't a valid log region.
        None
    } else {
        let global_metadata = deserialize_global_metadata(mem);
        let global_crc = deserialize_global_crc(mem);
        if global_crc != global_metadata.spec_crc() {
            // To be valid, the global metadata CRC has to be a valid CRC of the global metadata
            // encoded as bytes.
            None
        } else {
            if global_metadata.program_guid != LOG_PROGRAM_GUID {
                // To be valid, the global metadata has to refer to this program's GUID.
                // Otherwise, it wasn't created by this program.
                None
            } else if global_metadata.version_number == 1 {
                // If this metadata was written by version #1 of this code, then this is how to
                // interpret it:
                if mem.len() < ABSOLUTE_POS_OF_LOG_CDB + u64::spec_size_of() {
                    // If memory isn't big enough to store the CDB, then this region isn't
                    // valid.
                    None
                } else {
                    // Extract and parse the log metadata CDB
                    deserialize_and_check_log_cdb(mem)
                }
            } else {
                // This version of the code doesn't know how to parse metadata for any other
                // versions of this code besides 1. If we reach this point, we're presumably
                // reading metadata written by a future version of this code, which we can't
                // interpret.
                None
            }
        }
    }
}

pub open spec fn recover_state(mem: Seq<u8>, log_id: u128) -> Option<AbstractLogState> {
    // To recover, first recover the CDB, then use it to recover the abstract state.
    match recover_cdb(mem) {
        Some(cdb) => recover_given_cdb(mem, log_id, cdb),
        None => None,
    }
}

#[verifier::external_body]
pub proof fn lemma_establish_subrange_equivalence(mem1: Seq<u8>, mem2: Seq<u8>)
    ensures
        forall|i: int, j: int|
            mem1.subrange(i, j) =~= mem2.subrange(i, j) ==> #[trigger] mem1.subrange(i, j)
                == #[trigger] mem2.subrange(i, j),
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn lemma_if_only_differences_in_memory_are_inactive_metadata_then_recover_state_matches(
    mem1: Seq<u8>,
    mem2: Seq<u8>,
    log_id: u128,
    cdb: bool,
)
    requires
        mem1.len() == mem2.len() >= ABSOLUTE_POS_OF_LOG_AREA,
        recover_cdb(mem1) == Some(cdb),
        metadata_types_set(mem1),
        ({
            let unused_metadata_start = if cdb {
                ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE
            } else {
                ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_TRUE
            };
            let unused_metadata_end = unused_metadata_start + LogMetadata::spec_size_of()
                + u64::spec_size_of();
            forall|addr: int|
                0 <= addr < mem1.len() && !(unused_metadata_start <= addr < unused_metadata_end)
                    ==> mem1[addr] == mem2[addr]
        }),
    ensures
        recover_cdb(mem2) == Some(cdb),
        recover_state(mem1, log_id) == recover_state(mem2, log_id),
        metadata_types_set(mem2),
{
    unimplemented!()
}

/*log\logimpl_t*/

pub open spec fn can_only_crash_as_state(
    pm_region_view: PersistentMemoryRegionView,
    log_id: u128,
    state: AbstractLogState,
) -> bool {
    forall|s| #[trigger]
        pm_region_view.can_crash_as(s) ==> UntrustedLogImpl::recover(s, log_id) == Some(state)
}

pub struct TrustedPermission {
    ghost is_state_allowable: spec_fn(Seq<u8>) -> bool,
}

impl CheckPermission<Seq<u8>> for TrustedPermission {
    #[verifier::external_body]
    closed spec fn check_permission(&self, state: Seq<u8>) -> bool {
        unimplemented!()
    }
}

/*log\logimpl_v*/

pub struct LogInfo {
    pub log_area_len: u64,
    pub head: u128,
    pub head_log_area_offset: u64,
    pub log_length: u64,
    pub log_plus_pending_length: u64,
}

pub struct UntrustedLogImpl {
    cdb: bool,
    info: LogInfo,
    state: Ghost<AbstractLogState>,
}

impl UntrustedLogImpl {
    pub closed spec fn recover(mem: Seq<u8>, log_id: u128) -> Option<AbstractLogState> {
        if !metadata_types_set(mem) {
            // If the metadata types aren't properly set up, the log is unrecoverable.
            None
        } else {
            recover_state(mem, log_id)
        }
    }

    pub closed spec fn inv<Perm, PMRegion>(
        &self,
        wrpm_region: &WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        log_id: u128,
    ) -> bool where Perm: CheckPermission<Seq<u8>>, PMRegion: PersistentMemoryRegion {
        &&& wrpm_region.inv()  // whatever the persistent memory regions require as an invariant
        &&& no_outstanding_writes_to_metadata(wrpm_region@)
        &&& memory_matches_deserialized_cdb(wrpm_region@, self.cdb)
        &&& metadata_consistent_with_info(wrpm_region@, log_id, self.cdb, self.info)
        &&& info_consistent_with_log_area_in_region(wrpm_region@, self.info, self.state@)
        &&& can_only_crash_as_state(wrpm_region@, log_id, self.state@.drop_pending_appends())
        &&& metadata_types_set(wrpm_region@.committed())
    }

    #[verifier::external_body]
    exec fn update_inactive_log_metadata<PMRegion>(
        &self,
        wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<TrustedPermission, PMRegion>,
        subregion: &WriteRestrictedPersistentMemorySubregion,
        Ghost(log_id): Ghost<u128>,
        Ghost(prev_info): Ghost<LogInfo>,
        Ghost(prev_state): Ghost<AbstractLogState>,
        Tracked(perm): Tracked<&TrustedPermission>,
    ) where PMRegion: PersistentMemoryRegion
        requires
            subregion.inv(old(wrpm_region), perm),
            subregion.len() == LogMetadata::spec_size_of() + u64::spec_size_of(),
            subregion.view(old(wrpm_region)).no_outstanding_writes(),
            forall|addr: int| #[trigger] subregion.is_writable_absolute_addr_fn()(addr),
        ensures
            subregion.inv(wrpm_region, perm),
            ({
                let state_after_flush = subregion.view(wrpm_region).flush().committed();
                let log_metadata_bytes = extract_bytes(
                    state_after_flush,
                    0,
                    LogMetadata::spec_size_of(),
                );
                let log_crc_bytes = extract_bytes(
                    state_after_flush,
                    LogMetadata::spec_size_of(),
                    u64::spec_size_of(),
                );
                let log_metadata = LogMetadata::spec_from_bytes(log_metadata_bytes);
                let log_crc = u64::spec_from_bytes(log_crc_bytes);
                let new_metadata = LogMetadata {
                    head: self.info.head,
                    _padding: 0,
                    log_length: self.info.log_length,
                };
                let new_crc = new_metadata.spec_crc();

                &&& log_crc == log_metadata.spec_crc()
                &&& log_metadata.head == self.info.head
                &&& log_metadata.log_length == self.info.log_length
                &&& log_metadata_bytes == new_metadata.spec_to_bytes()
                &&& log_crc_bytes == new_crc.spec_to_bytes()
            }),
    {
        unimplemented!()
    }

    exec fn update_log_metadata<PMRegion>(
        &mut self,
        wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<TrustedPermission, PMRegion>,
        Ghost(log_id): Ghost<u128>,
        Ghost(prev_info): Ghost<LogInfo>,
        Ghost(prev_state): Ghost<AbstractLogState>,
        Tracked(perm): Tracked<&TrustedPermission>,
    ) where PMRegion: PersistentMemoryRegion
        requires
            old(wrpm_region).inv(),
            memory_matches_deserialized_cdb(old(wrpm_region)@, old(self).cdb),
            no_outstanding_writes_to_metadata(old(wrpm_region)@),
            metadata_consistent_with_info(old(wrpm_region)@, log_id, old(self).cdb, prev_info),
            info_consistent_with_log_area_in_region(
                old(wrpm_region)@.flush(),
                old(self).info,
                old(self).state@,
            ),
            info_consistent_with_log_area_in_region(old(wrpm_region)@, prev_info, prev_state),
            old(self).info.log_area_len == prev_info.log_area_len,
            forall|s|
                {
                    ||| Self::recover(s, log_id) == Some(prev_state.drop_pending_appends())
                    ||| Self::recover(s, log_id) == Some(old(self).state@.drop_pending_appends())
                } ==> #[trigger] perm.check_permission(s),
            metadata_types_set(old(wrpm_region)@.committed()),
        ensures
            self.inv(wrpm_region, log_id),
            wrpm_region.constants() == old(wrpm_region).constants(),
            self.state == old(self).state,
    {
        broadcast use pmcopy_axioms;

        reveal(spec_padding_needed);

        // Set the `unused_metadata_pos` to be the position corresponding to !self.cdb
        // since we're writing in the inactive part of the metadata.

        let ghost old_wrpm = wrpm_region@;
        let unused_metadata_pos = if self.cdb {
            ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE
        } else {
            ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_TRUE
        };
        assert(unused_metadata_pos == get_log_metadata_pos(!self.cdb));

        // Update the inactive log metadata by creating a
        // subregion and invoking `update_inactive_log_metadata`.
        // The main interesting part of creating the subregion is
        // establishing a condition `condition` such that (1)
        // `condition(crash_state) ==>
        // perm.check_permission(crash_state)` and (2) `condition`
        // is preserved by updating writable addresses within the
        // subregion.

        let ghost is_writable_absolute_addr_fn = |addr: int| true;
        let ghost condition = |mem: Seq<u8>|
            {
                &&& mem.len() >= ABSOLUTE_POS_OF_LOG_AREA
                &&& recover_cdb(mem) == Some(self.cdb)
                &&& recover_state(mem, log_id) == Some(prev_state.drop_pending_appends())
                &&& metadata_types_set(mem)
            };
        assert forall|s1: Seq<u8>, s2: Seq<u8>|
            {
                &&& condition(s1)
                &&& s1.len() == s2.len() == wrpm_region@.len()
                &&& #[trigger] memories_differ_only_where_subregion_allows(
                    s1,
                    s2,
                    unused_metadata_pos as nat,
                    LogMetadata::spec_size_of() + u64::spec_size_of(),
                    is_writable_absolute_addr_fn,
                )
            } implies condition(s2) by {
            lemma_if_only_differences_in_memory_are_inactive_metadata_then_recover_state_matches(
                s1,
                s2,
                log_id,
                self.cdb,
            );
        }
        assert forall|crash_state: Seq<u8>|
            wrpm_region@.can_crash_as(crash_state) implies condition(crash_state) by {
            lemma_invariants_imply_crash_recover_forall(
                wrpm_region@,
                log_id,
                self.cdb,
                prev_info,
                prev_state,
            );
        }
        let subregion = WriteRestrictedPersistentMemorySubregion::new_with_condition(
            wrpm_region,
            Tracked(perm),
            unused_metadata_pos,
            Ghost(LogMetadata::spec_size_of() + u64::spec_size_of()),
            Ghost(is_writable_absolute_addr_fn),
            Ghost(condition),
        );
        self.update_inactive_log_metadata(
            wrpm_region,
            &subregion,
            Ghost(log_id),
            Ghost(prev_info),
            Ghost(prev_state),
            Tracked(perm),
        );

        // We've updated the inactive log metadata now, so it's a good time to
        // mention some relevant facts about the consequent state.

        proof {
            let mem1 = old_wrpm.committed();
            let mem2 = wrpm_region@.committed();
            subregion.lemma_reveal_opaque_inv(wrpm_region, perm);
            lemma_establish_subrange_equivalence(mem1, mem2);

            assert(wrpm_region.inv());
            assert(wrpm_region.constants() == old(wrpm_region).constants());
            assert(unused_metadata_pos == get_log_metadata_pos(!self.cdb));
            assert(memory_matches_deserialized_cdb(wrpm_region@, self.cdb));
            assert(metadata_consistent_with_info(wrpm_region@, log_id, self.cdb, prev_info));
            assert(info_consistent_with_log_area_in_region(wrpm_region@, prev_info, prev_state));
            assert(info_consistent_with_log_area_in_region(
                wrpm_region@.flush(),
                self.info,
                self.state@,
            ));
            assert(forall|s|
                Self::recover(s, log_id) == Some(prev_state.drop_pending_appends())
                    ==> #[trigger] perm.check_permission(s));
            assert(self.info.log_area_len == prev_info.log_area_len);
            assert(metadata_consistent_with_info(
                wrpm_region@.flush(),
                log_id,
                !self.cdb,
                self.info,
            )) by {
                let mem3 = wrpm_region@.flush().committed();
                lemma_establish_subrange_equivalence(mem1, mem3);
                assert(extract_bytes(mem3, unused_metadata_pos as nat, LogMetadata::spec_size_of())
                    =~= extract_bytes(
                    subregion.view(wrpm_region).flush().committed(),
                    0,
                    LogMetadata::spec_size_of(),
                ));
                assert(extract_bytes(
                    mem3,
                    unused_metadata_pos as nat + LogMetadata::spec_size_of(),
                    u64::spec_size_of(),
                ) =~= extract_bytes(
                    subregion.view(wrpm_region).flush().committed(),
                    LogMetadata::spec_size_of(),
                    u64::spec_size_of(),
                ));
            }

            assert(inactive_metadata_types_set(wrpm_region@.flush().committed())) by {
                let mem = wrpm_region@.flush().committed();

                lemma_flushing_metadata_maintains_invariants(
                    wrpm_region@,
                    log_id,
                    self.cdb,
                    prev_info,
                    prev_state,
                );

                // Construct the new inactive log metadata contents to show that the types for the inactive metadata
                // and crc are set.
                let new_metadata = LogMetadata {
                    head: self.info.head,
                    _padding: 0,
                    log_length: self.info.log_length,
                };
                let new_crc = new_metadata.spec_crc();

                let inactive_metadata_pos = get_log_metadata_pos(!self.cdb);
                assert(extract_bytes(mem, inactive_metadata_pos as nat, LogMetadata::spec_size_of())
                    == new_metadata.spec_to_bytes());
                assert(extract_bytes(
                    mem,
                    inactive_metadata_pos as nat + LogMetadata::spec_size_of(),
                    u64::spec_size_of(),
                ) == new_crc.spec_to_bytes());
            }
        }

        // Prove that after the flush we're about to do, all our
        // invariants will continue to hold (using the still-unchanged
        // CDB and the old metadata, infos, and state).

        proof {
            lemma_flushing_metadata_maintains_invariants(
                wrpm_region@,
                log_id,
                self.cdb,
                prev_info,
                prev_state,
            );
        }

        // Next, flush all outstanding writes to memory. This is
        // necessary so that those writes are ordered before the update
        // to the CDB.
        wrpm_region.flush();

        // Next, compute the new encoded CDB to write.
        let new_cdb = if self.cdb {
            CDB_FALSE
        } else {
            CDB_TRUE
        };
        let ghost new_cdb_bytes = new_cdb.spec_to_bytes();

        // Show that after writing and flushing, the CDB will be !self.cdb

        let ghost pm_region_after_write = wrpm_region@.write(
            ABSOLUTE_POS_OF_LOG_CDB as int,
            new_cdb_bytes,
        );
        let ghost flushed_mem_after_write = pm_region_after_write.flush();
        assert(memory_matches_deserialized_cdb(flushed_mem_after_write, !self.cdb)) by {
            let flushed_region = pm_region_after_write.flush();
            lemma_write_reflected_after_flush_committed(
                wrpm_region@,
                ABSOLUTE_POS_OF_LOG_CDB as int,
                new_cdb_bytes,
            );
        }

        // Show that after writing and flushing, our invariants will
        // hold for each log if we flip `self.cdb`.

        let ghost pm_region_after_flush = pm_region_after_write.flush();
        assert({
            &&& metadata_consistent_with_info(pm_region_after_flush, log_id, !self.cdb, self.info)
            &&& info_consistent_with_log_area_in_region(
                pm_region_after_flush,
                self.info,
                self.state@,
            )
            &&& metadata_types_set(pm_region_after_flush.committed())
        }) by {
            lemma_establish_subrange_equivalence(
                wrpm_region@.committed(),
                pm_region_after_flush.committed(),
            );

            lemma_metadata_consistent_with_info_after_cdb_update(
                wrpm_region@,
                pm_region_after_flush,
                log_id,
                new_cdb_bytes,
                !self.cdb,
                self.info,
            );
            lemma_metadata_types_set_after_cdb_update(
                wrpm_region@,
                pm_region_after_flush,
                log_id,
                new_cdb_bytes,
                self.cdb,
            )
        }
        assert(memory_matches_deserialized_cdb(pm_region_after_flush, !self.cdb));

        // Show that if we crash after the write and flush, we recover
        // to an abstract state corresponding to `self.state@` after
        // dropping pending appends.

        proof {
            lemma_invariants_imply_crash_recover_forall(
                pm_region_after_flush,
                log_id,
                !self.cdb,
                self.info,
                self.state@,
            );
        }

        // Show that if we crash after initiating the write of the CDB,
        // we'll recover to a permissible state. There are two cases:
        //
        // If we crash without any updating, then we'll recover to
        // state `prev_state.drop_pending_appends()` with the current
        // CDB.
        //
        // If we crash after writing, then we'll recover to state
        // `self.state@.drop_pending_appends()` with the flipped CDB.
        //
        // Because we're only writing within the persistence
        // granularity of the persistent memory, a crash in the middle
        // will either leave the persistent memory in the pre-state or
        // the post-state.
        //
        // This means we're allowed to do the write because if we
        // crash, we'll either be in state wrpm_region@.committed() or
        // pm_region_after_write.flush().committed(). In the former
        // case, we'll be in state `prev_state.drop_pending_appends()`
        // and in the latter case, as shown above, we'll be in state
        // `self.state@.drop_pending_appends()`.

        assert forall|crash_bytes|
            pm_region_after_write.can_crash_as(
                crash_bytes,
            ) implies #[trigger] perm.check_permission(crash_bytes) by {
            lemma_invariants_imply_crash_recover_forall(
                wrpm_region@,
                log_id,
                self.cdb,
                prev_info,
                prev_state,
            );
            lemma_single_write_crash_effect_on_pm_region_view(
                wrpm_region@,
                ABSOLUTE_POS_OF_LOG_CDB as int,
                new_cdb_bytes,
            );
            if crash_bytes == wrpm_region@.committed() {
                assert(wrpm_region@.can_crash_as(crash_bytes));
            } else {
                assert(pm_region_after_flush.can_crash_as(crash_bytes));
            }
        }

        // Finally, update the CDB, then flush, then flip `self.cdb`.
        // There's no need to flip `self.cdb` atomically with the write
        // since the flip of `self.cdb` is happening in local
        // non-persistent memory so if we crash it'll be lost anyway.
        // wrpm_region.write(0, ABSOLUTE_POS_OF_LOG_CDB, new_cdb.as_slice(), Tracked(perm));
        wrpm_region.serialize_and_write(ABSOLUTE_POS_OF_LOG_CDB, &new_cdb, Tracked(perm));
        wrpm_region.flush();
        self.cdb = !self.cdb;
    }
}

} // verus!
