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

pub open spec fn active_metadata_is_equal(
    pm_region_view1: PersistentMemoryRegionView,
    pm_region_view2: PersistentMemoryRegionView,
) -> bool {
    let pm_bytes1 = pm_region_view1.committed();
    let pm_bytes2 = pm_region_view2.committed();
    active_metadata_bytes_are_equal(pm_bytes1, pm_bytes2)
}

pub open spec fn active_metadata_bytes_are_equal(pm_bytes1: Seq<u8>, pm_bytes2: Seq<u8>) -> bool {
    let cdb1 = deserialize_and_check_log_cdb(pm_bytes1);
    let cdb2 = deserialize_and_check_log_cdb(pm_bytes2);
    &&& cdb1.is_Some()
    &&& cdb2.is_Some()
    &&& cdb1 == cdb2
    &&& pm_bytes1.subrange(
        ABSOLUTE_POS_OF_GLOBAL_METADATA as int,
        ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as int,
    ) == pm_bytes2.subrange(
        ABSOLUTE_POS_OF_GLOBAL_METADATA as int,
        ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as int,
    )
    &&& {
        let metadata_pos = if cdb1.unwrap() {
            ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_TRUE as int
        } else {
            ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as int
        };
        pm_bytes1.subrange(
            metadata_pos,
            metadata_pos + LogMetadata::spec_size_of() + u64::spec_size_of(),
        ) == pm_bytes2.subrange(
            metadata_pos,
            metadata_pos + LogMetadata::spec_size_of() + u64::spec_size_of(),
        )
    }
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
    &&& pm_region_view.no_outstanding_writes_in_range(
        ABSOLUTE_POS_OF_GLOBAL_METADATA as int,
        ABSOLUTE_POS_OF_LOG_CDB as int,
    )
    &&& pm_region_view.no_outstanding_writes_in_range(
        get_log_metadata_pos(cdb) as int,
        get_log_crc_end(cdb) as int,
    )
    &&& global_crc == global_metadata.spec_crc()
    &&& region_crc == region_metadata.spec_crc()
    &&& log_crc == log_metadata.spec_crc()
    &&& global_metadata.program_guid == LOG_PROGRAM_GUID
    &&& global_metadata.version_number == LOG_PROGRAM_VERSION_NUMBER
    &&& global_metadata.length_of_region_metadata == RegionMetadata::spec_size_of()
    &&& region_metadata.region_size == mem.len()
    &&& region_metadata.log_id == log_id
    &&& region_metadata.log_area_len == info.log_area_len
    &&& log_metadata.head == info.head
    &&& log_metadata.log_length == info.log_length
    &&& mem.len() >= ABSOLUTE_POS_OF_LOG_AREA + info.log_area_len
}

pub open spec fn info_consistent_with_log_area(
    log_area_view: PersistentMemoryRegionView,
    info: LogInfo,
    state: AbstractLogState,
) -> bool {
    &&& info.log_area_len >= MIN_LOG_AREA_SIZE
    &&& info.log_length <= info.log_plus_pending_length <= info.log_area_len
    &&& info.head_log_area_offset == info.head as int % info.log_area_len as int
    &&& info.head + info.log_plus_pending_length <= u128::MAX
    &&& state.log.len() == info.log_length
    &&& state.pending.len() == info.log_plus_pending_length - info.log_length
    &&& state.head == info.head
    &&& state.capacity == info.log_area_len
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
pub proof fn lemma_metadata_matches_implies_metadata_types_set(
    pm1: PersistentMemoryRegionView,
    pm2: PersistentMemoryRegionView,
    cdb: bool,
)
    requires
        no_outstanding_writes_to_active_metadata(pm1, cdb),
        no_outstanding_writes_to_active_metadata(pm2, cdb),
        metadata_types_set(pm1.committed()),
        memory_matches_deserialized_cdb(pm1, cdb),
        0 < ABSOLUTE_POS_OF_LOG_AREA < pm1.committed().len(),
        0 < ABSOLUTE_POS_OF_LOG_AREA < pm2.committed().len(),
        active_metadata_is_equal(pm1, pm2),
        pm1.len() == pm2.len(),
    ensures
        metadata_types_set(pm2.committed()),
{
    unimplemented!()
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
#[derive(PmSized, Copy, Clone,
    Default)]
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

#[verifier::external_body]
pub proof fn lemma_establish_subrange_equivalence(mem1: Seq<u8>, mem2: Seq<u8>)
    ensures
        forall|i: int, j: int|
            mem1.subrange(i, j) =~= mem2.subrange(i, j) ==> #[trigger] mem1.subrange(i, j)
                == #[trigger] mem2.subrange(i, j),
{
    unimplemented!()
}

pub struct LogInfo {
    pub log_area_len: u64,
    pub head: u128,
    pub head_log_area_offset: u64,
    pub log_length: u64,
    pub log_plus_pending_length: u64,
}

pub struct AbstractLogState {
    pub head: int,
    pub log: Seq<u8>,
    pub pending: Seq<u8>,
    pub capacity: int,
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



pub trait PmCopy: PmSized + SpecPmSized + Sized + Copy {

}

pub trait PmCopyHelper: PmCopy {
    spec fn spec_to_bytes(self) -> Seq<u8>;

    spec fn spec_from_bytes(bytes: Seq<u8>) -> Self;

    spec fn bytes_parseable(bytes: Seq<u8>) -> bool;

    spec fn spec_crc(self) -> u64;
}

impl<T> PmCopyHelper for T where T: PmCopy {
    closed spec fn spec_to_bytes(self) -> Seq<u8>;

    closed spec fn spec_from_bytes(bytes: Seq<u8>) -> Self {
        choose|x: T| x.spec_to_bytes() == bytes
    }

    open spec fn spec_crc(self) -> u64 {
        spec_crc_u64(self.spec_to_bytes())
    }

    open spec fn bytes_parseable(bytes: Seq<u8>) -> bool {
        Self::spec_from_bytes(bytes).spec_to_bytes() == bytes
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

    pub open spec fn committed(self) -> Seq<u8> {
        self.state.map(|_addr, b: PersistentMemoryByte| b.state_at_last_flush)
    }
}

pub open spec fn extract_bytes(bytes: Seq<u8>, pos: nat, len: nat) -> Seq<u8> {
    bytes.subrange(pos as int, (pos + len) as int)
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
pub proof fn lemma_updating_inactive_metadata_maintains_invariants(
    pm_region_view: PersistentMemoryRegionView,
    log_id: u128,
    cdb: bool,
    info: LogInfo,
    state: AbstractLogState,
    bytes_to_write: Seq<u8>,
)
    requires
        memory_matches_deserialized_cdb(pm_region_view, cdb),
        metadata_consistent_with_info(pm_region_view, log_id, cdb, info),
        info_consistent_with_log_area_in_region(pm_region_view, info, state),
        bytes_to_write.len() == LogMetadata::spec_size_of(),
        metadata_types_set(pm_region_view.committed()),
    ensures
        ({
            let pm_region_view2 = pm_region_view.write(
                get_log_metadata_pos(!cdb) as int,
                bytes_to_write,
            );
            &&& memory_matches_deserialized_cdb(pm_region_view2, cdb)
            &&& metadata_consistent_with_info(pm_region_view2, log_id, cdb, info)
            &&& info_consistent_with_log_area_in_region(pm_region_view2, info, state)
            &&& metadata_types_set(pm_region_view2.committed())
        }),
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
