use deps_hack::{pmsized_primitive, PmSized};
use vstd::prelude::*;
verus! {

pub open spec fn no_outstanding_writes_to_active_metadata(
    pm_region_view: PersistentMemoryRegionView,
    cdb: bool,
) -> bool {
    let metadata_pos = if cdb {
        ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_TRUE as int
    } else {
        ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as int
    };
    &&& pm_region_view.no_outstanding_writes_in_range(
        metadata_pos,
        metadata_pos + LogMetadata::spec_size_of() + u64::spec_size_of(),
    )
    &&& pm_region_view.no_outstanding_writes_in_range(
        ABSOLUTE_POS_OF_GLOBAL_METADATA as int,
        ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as int,
    )
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
#[derive(PmSized,
    Copy, Clone, Default)]
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

    spec fn bytes_parseable(bytes: Seq<u8>) -> bool;
}

impl<T> PmCopyHelper for T where T: PmCopy {
    closed spec fn spec_to_bytes(self) -> Seq<u8>;

    closed spec fn spec_from_bytes(bytes: Seq<u8>) -> Self {
        choose|x: T| x.spec_to_bytes() == bytes
    }

    open spec fn bytes_parseable(bytes: Seq<u8>) -> bool {
        Self::spec_from_bytes(bytes).spec_to_bytes() == bytes
    }
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
pub open spec fn spec_padding_needed(offset: nat, align: nat) -> nat
    {
        let misalignment = offset % align;
        if misalignment > 0 {
            (align - misalignment) as nat
        } else {
            0
        }
    }

pub closed spec fn spec_crc_u64(bytes: Seq<u8>) -> u64;

pub const CDB_FALSE: u64 = 0xa32842d19001605e;

pub const CDB_TRUE: u64 = 0xab21aa73069531b7;

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

pub open spec fn extract_bytes(bytes: Seq<u8>, pos: nat, len: nat) -> Seq<u8> {
    bytes.subrange(pos as int, (pos + len) as int)
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

#[verifier::auto_ext_equal(assert, assert_by, ensures)]
pub proof fn lemma_metadata_set_after_crash(pm_region_view: PersistentMemoryRegionView, cdb: bool)
    requires
        no_outstanding_writes_to_active_metadata(pm_region_view, cdb),
        metadata_types_set(pm_region_view.committed()),
        memory_matches_deserialized_cdb(pm_region_view, cdb),
    ensures
        forall|s|
            #![auto]
            {
                &&& pm_region_view.can_crash_as(s)
                &&& 0 <= ABSOLUTE_POS_OF_GLOBAL_METADATA < ABSOLUTE_POS_OF_LOG_AREA < s.len()
            } ==> metadata_types_set(s),
{
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
