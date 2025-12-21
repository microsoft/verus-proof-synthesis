#![feature(new_uninit)]
use deps_hack::{pmsized_primitive, PmSized};
use std::mem::MaybeUninit;
use vstd::prelude::*;
verus! {

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
        None
    } else {
        let global_metadata = deserialize_global_metadata(mem);
        let global_crc = deserialize_global_crc(mem);
        if global_crc != global_metadata.spec_crc() {
            None
        } else {
            if global_metadata.program_guid != LOG_PROGRAM_GUID {
                None
            } else if global_metadata.version_number == 1 {
                if global_metadata.length_of_region_metadata != RegionMetadata::spec_size_of() {
                    None
                } else {
                    let region_metadata = deserialize_region_metadata(mem);
                    let region_crc = deserialize_region_crc(mem);
                    if region_crc != region_metadata.spec_crc() {
                        None
                    } else {
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
                None
            }
        }
    }
}

pub enum LogErr {
    InsufficientSpaceForSetup { required_space: u64 },
    StartFailedDueToLogIDMismatch { log_id_expected: u128, log_id_read: u128 },
    StartFailedDueToRegionSizeMismatch { region_size_expected: u64, region_size_read: u64 },
    StartFailedDueToProgramVersionNumberUnsupported { version_number: u64, max_supported: u64 },
    StartFailedDueToInvalidMemoryContents,
    CRCMismatch,
    InsufficientSpaceForAppend { available_space: u64 },
    CantReadBeforeHead { head: u128 },
    CantReadPastTail { tail: u128 },
    CantAdvanceHeadPositionBeforeHead { head: u128 },
    CantAdvanceHeadPositionBeyondTail { tail: u128 },
    PmemErr { err: PmemError },
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

impl PmCopy for u64 {

}

#[verifier::external_body]
#[verifier::reject_recursive_types(S)]
pub struct MaybeCorruptedBytes<S> where S: PmCopy {
    val: Box<MaybeUninit<S>>,
}

impl<S> MaybeCorruptedBytes<S> where S: PmCopy {
    pub closed spec fn view(self) -> Seq<u8>;

    #[verifier::external_body]
    pub exec fn as_slice(&self) -> (out: &[u8])
        ensures
            out@ == self@,
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub exec fn extract_init_val(
        self,
        Ghost(true_val): Ghost<S>,
        Ghost(true_bytes): Ghost<Seq<u8>>,
        Ghost(impervious_to_corruption): Ghost<bool>,
    ) -> (out: Box<S>)
        requires
            if impervious_to_corruption {
                true
            } else {
                &&& true_bytes == true_val.spec_to_bytes()
                &&& self@ == true_bytes
            },
        ensures
            out == true_val,
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub exec fn new() -> (out: Self) {
        MaybeCorruptedBytes { val: Box::<S>::new_uninit() }
    }
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

pub enum PmemError {
    InvalidFileName,
    CannotOpenPmFile,
    NotPm,
    PmdkError,
    AccessOutOfRange,
}

pub closed spec fn maybe_corrupted_byte(byte: u8, true_byte: u8, addr: int) -> bool;

pub open spec fn all_elements_unique(seq: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < seq.len() ==> seq[i] != seq[j]
}

pub open spec fn maybe_corrupted(bytes: Seq<u8>, true_bytes: Seq<u8>, addrs: Seq<int>) -> bool {
    &&& bytes.len() == true_bytes.len() == addrs.len()
    &&& forall|i: int|
        #![auto]
        0 <= i < bytes.len() ==> maybe_corrupted_byte(bytes[i], true_bytes[i], addrs[i])
}

pub open spec fn spec_crc_bytes(bytes: Seq<u8>) -> Seq<u8> {
    spec_crc_u64(bytes).spec_to_bytes()
}

pub closed spec fn spec_crc_u64(bytes: Seq<u8>) -> u64;

pub const CDB_FALSE: u64 = 0xa32842d19001605e;

pub const CDB_TRUE: u64 = 0xab21aa73069531b7;

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

#[verifier::ext_equal]
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

    pub open spec fn no_outstanding_writes(self) -> bool {
        Self::no_outstanding_writes_in_range(self, 0, self.state.len() as int)
    }

    pub open spec fn committed(self) -> Seq<u8> {
        self.state.map(|_addr, b: PersistentMemoryByte| b.state_at_last_flush)
    }
}

pub struct PersistentMemoryConstants {
    pub impervious_to_corruption: bool,
}

pub trait PersistentMemoryRegion: Sized {
    spec fn view(&self) -> PersistentMemoryRegionView;

    spec fn inv(&self) -> bool;

    spec fn constants(&self) -> PersistentMemoryConstants;

    fn get_region_size(&self) -> (result: u64)
        requires
            self.inv(),
        ensures
            result == self@.len(),
    ;

    fn read_aligned<S>(&self, addr: u64) -> (bytes: Result<
        MaybeCorruptedBytes<S>,
        PmemError,
    >) where S: PmCopy + Sized
        requires
            self.inv(),
            0 <= addr < addr + S::spec_size_of() <= self@.len(),
            self@.no_outstanding_writes_in_range(addr as int, addr + S::spec_size_of()),
            S::bytes_parseable(self@.committed().subrange(addr as int, addr + S::spec_size_of())),
        ensures
            match bytes {
                Ok(bytes) => {
                    let true_bytes = self@.committed().subrange(
                        addr as int,
                        addr + S::spec_size_of(),
                    );
                    let addrs = Seq::<int>::new(S::spec_size_of() as nat, |i: int| i + addr);
                    if self.constants().impervious_to_corruption {
                        bytes@ == true_bytes
                    } else {
                        maybe_corrupted(bytes@, true_bytes, addrs)
                    }
                },
                _ => false,
            },
    ;
}

pub open spec fn extract_bytes(bytes: Seq<u8>, pos: nat, len: nat) -> Seq<u8> {
    bytes.subrange(pos as int, (pos + len) as int)
}

#[verifier::external_body]
pub fn check_crc(
    data_c: &[u8],
    crc_c: &[u8],
    Ghost(mem): Ghost<Seq<u8>>,
    Ghost(impervious_to_corruption): Ghost<bool>,
    Ghost(data_addrs): Ghost<Seq<int>>,
    Ghost(crc_addrs): Ghost<Seq<int>>,
) -> (b: bool)
    requires
        data_addrs.len() <= mem.len(),
        crc_addrs.len() <= mem.len(),
        crc_c@.len() == u64::spec_size_of(),
        all_elements_unique(data_addrs),
        all_elements_unique(crc_addrs),
        ({
            let true_data_bytes = Seq::new(data_addrs.len(), |i: int| mem[data_addrs[i] as int]);
            let true_crc_bytes = Seq::new(crc_addrs.len(), |i: int| mem[crc_addrs[i]]);
            &&& if impervious_to_corruption {
                &&& data_c@ == true_data_bytes
                &&& crc_c@ == true_crc_bytes
            } else {
                &&& maybe_corrupted(data_c@, true_data_bytes, data_addrs)
                &&& maybe_corrupted(crc_c@, true_crc_bytes, crc_addrs)
            }
        }),
    ensures
        ({
            let true_data_bytes = Seq::new(data_addrs.len(), |i: int| mem[data_addrs[i] as int]);
            let true_crc_bytes = Seq::new(crc_addrs.len(), |i: int| mem[crc_addrs[i]]);
            true_crc_bytes == spec_crc_bytes(true_data_bytes) ==> {
                if b {
                    &&& data_c@ == true_data_bytes
                    &&& crc_c@ == true_crc_bytes
                } else {
                    !impervious_to_corruption
                }
            }
        }),
{
    unimplemented!()
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

pub struct PersistentMemorySubregion {
    start_: u64,
    len_: Ghost<nat>,
}

impl PersistentMemorySubregion {
    #[verifier::external_body]
    pub exec fn new<PMRegion: PersistentMemoryRegion>(
        pm: &PMRegion,
        start: u64,
        Ghost(len): Ghost<nat>,
    ) -> (result: Self)
        requires
            pm.inv(),
            start + len <= pm@.len() <= u64::MAX,
        ensures
            result.start() == start,
            result.len() == len,
            result.view(pm) == get_subregion_view(pm@, start as nat, len),
    {
        unimplemented!()
    }

    pub closed spec fn start(self) -> nat {
        self.start_ as nat
    }

    pub closed spec fn len(self) -> nat {
        self.len_@
    }

    #[verifier::external_body]
    pub closed spec fn view<PMRegion: PersistentMemoryRegion>(
        self,
        pm: &PMRegion,
    ) -> PersistentMemoryRegionView {
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

#[verifier::auto_ext_equal(assert, assert_by, ensures)]
pub fn read_log_variables<PMRegion: PersistentMemoryRegion>(
    pm_region: &PMRegion,
    log_id: u128,
    cdb: bool,
) -> (result: Result<LogInfo, LogErr>)
    requires
        pm_region.inv(),
        pm_region@.no_outstanding_writes(),
        metadata_types_set(pm_region@.committed()),
        cdb == deserialize_and_check_log_cdb(pm_region@.committed()).unwrap(),
    ensures
        ({
            let state = recover_given_cdb(pm_region@.committed(), log_id, cdb);
            match result {
                Ok(info) => state.is_Some() ==> {
                    &&& metadata_consistent_with_info(pm_region@, log_id, cdb, info)
                    &&& info_consistent_with_log_area_in_region(pm_region@, info, state.unwrap())
                },
                Err(LogErr::CRCMismatch) => state.is_Some()
                    ==> !pm_region.constants().impervious_to_corruption,
                Err(LogErr::StartFailedDueToInvalidMemoryContents) => {
                    ||| pm_region@.len() < ABSOLUTE_POS_OF_LOG_AREA + MIN_LOG_AREA_SIZE
                    ||| state is None
                },
                Err(
                    LogErr::StartFailedDueToProgramVersionNumberUnsupported {
                        version_number,
                        max_supported,
                    },
                ) => {
                    &&& state is None
                    &&& version_number != max_supported
                },
                Err(LogErr::StartFailedDueToLogIDMismatch { log_id_expected, log_id_read }) => {
                    &&& state is None
                    &&& log_id_expected != log_id_read
                },
                Err(
                    LogErr::StartFailedDueToRegionSizeMismatch {
                        region_size_expected,
                        region_size_read,
                    },
                ) => {
                    &&& state is None
                    &&& region_size_expected != region_size_read
                },
                _ => false,
            }
        }),
{
    let region_size = pm_region.get_region_size();
    if region_size < ABSOLUTE_POS_OF_LOG_AREA + MIN_LOG_AREA_SIZE {
        let ret = Err(LogErr::StartFailedDueToInvalidMemoryContents);
        return ret;
    }
    let global_metadata = match pm_region.read_aligned::<GlobalMetadata>(
        ABSOLUTE_POS_OF_GLOBAL_METADATA,
    ) {
        Ok(global_metadata) => global_metadata,
        Err(e) => {
            let ret = Err(LogErr::PmemErr { err: e });
            return ret;
        },
    };
    let global_crc = match pm_region.read_aligned::<u64>(ABSOLUTE_POS_OF_GLOBAL_CRC) {
        Ok(global_crc) => global_crc,
        Err(e) => {
            let ret = Err(LogErr::PmemErr { err: e });
            return ret;
        },
    };
    let ghost check_crc_ghost0: Seq<u8> = arbitrary(); // TODO - replace with correct value
    let ghost check_crc_ghost1: bool = arbitrary(); // TODO - replace with correct value
    let ghost check_crc_ghost2: Seq<int> = arbitrary(); // TODO - replace with correct value
    let ghost check_crc_ghost3: Seq<int> = arbitrary(); // TODO - replace with correct value
    if !check_crc(
        global_metadata.as_slice(),
        global_crc.as_slice(),
        Ghost(check_crc_ghost0),
        Ghost(check_crc_ghost1),
        Ghost(check_crc_ghost2),
        Ghost(check_crc_ghost3),
    ) {
        let ret = Err(LogErr::CRCMismatch);
        return ret;
    }
    let ghost extract_init_val_ghost0: GlobalMetadata = arbitrary(); // TODO - replace with correct value
    let ghost extract_init_val_ghost1: Seq<u8> = arbitrary(); // TODO - replace with correct value
    let ghost extract_init_val_ghost2: bool = arbitrary(); // TODO - replace with correct value
    let global_metadata = global_metadata.extract_init_val(
        Ghost(extract_init_val_ghost0),
        Ghost(extract_init_val_ghost1),
        Ghost(extract_init_val_ghost2),
    );
    if global_metadata.program_guid != LOG_PROGRAM_GUID {
        let ret = Err(LogErr::StartFailedDueToInvalidMemoryContents);
        return ret;
    }
    if global_metadata.version_number != LOG_PROGRAM_VERSION_NUMBER {
        let ret = Err(
            LogErr::StartFailedDueToProgramVersionNumberUnsupported {
                version_number: global_metadata.version_number,
                max_supported: LOG_PROGRAM_VERSION_NUMBER,
            },
        );
        return ret;
    }
    if global_metadata.length_of_region_metadata != size_of::<RegionMetadata>() as u64 {
        let ret = Err(LogErr::StartFailedDueToInvalidMemoryContents);
        return ret;
    }
    let region_metadata = match pm_region.read_aligned::<RegionMetadata>(
        ABSOLUTE_POS_OF_REGION_METADATA,
    ) {
        Ok(region_metadata) => region_metadata,
        Err(e) => {
            let ret = Err(LogErr::PmemErr { err: e });
            return ret;
        },
    };
    let region_crc = match pm_region.read_aligned::<u64>(ABSOLUTE_POS_OF_REGION_CRC) {
        Ok(region_crc) => region_crc,
        Err(e) => {
            let ret = Err(LogErr::PmemErr { err: e });
            return ret;
        },
    };
    let ghost check_crc_ghost4: Seq<u8> = arbitrary(); // TODO - replace with correct value
    let ghost check_crc_ghost5: bool = arbitrary(); // TODO - replace with correct value
    let ghost check_crc_ghost6: Seq<int> = arbitrary(); // TODO - replace with correct value
    let ghost check_crc_ghost7: Seq<int> = arbitrary(); // TODO - replace with correct value
    if !check_crc(
        region_metadata.as_slice(),
        region_crc.as_slice(),
        Ghost(check_crc_ghost4),
        Ghost(check_crc_ghost5),
        Ghost(check_crc_ghost6),
        Ghost(check_crc_ghost7),
    ) {
        let ret = Err(LogErr::CRCMismatch);
        return ret;
    }
    let ghost extract_init_val_ghost3: RegionMetadata = arbitrary(); // TODO - replace with correct value
    let ghost extract_init_val_ghost4: Seq<u8> = arbitrary(); // TODO - replace with correct value
    let ghost extract_init_val_ghost5: bool = arbitrary(); // TODO - replace with correct value
    let region_metadata = region_metadata.extract_init_val(
        Ghost(extract_init_val_ghost3),
        Ghost(extract_init_val_ghost4),
        Ghost(extract_init_val_ghost5),
    );
    if region_metadata.region_size != region_size {
        let ret = Err(
            LogErr::StartFailedDueToRegionSizeMismatch {
                region_size_expected: region_size,
                region_size_read: region_metadata.region_size,
            },
        );
        return ret;
    }
    if region_metadata.log_id != log_id {
        let ret = Err(
            LogErr::StartFailedDueToLogIDMismatch {
                log_id_expected: log_id,
                log_id_read: region_metadata.log_id,
            },
        );
        return ret;
    }
    if region_metadata.log_area_len > region_size {
        let ret = Err(LogErr::StartFailedDueToInvalidMemoryContents);
        return ret;
    }
    if region_size - region_metadata.log_area_len < ABSOLUTE_POS_OF_LOG_AREA {
        let ret = Err(LogErr::StartFailedDueToInvalidMemoryContents);
        return ret;
    }
    if region_metadata.log_area_len < MIN_LOG_AREA_SIZE {
        let ret = Err(LogErr::StartFailedDueToInvalidMemoryContents);
        return ret;
    }
    let log_metadata_pos = if cdb {
        ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_TRUE
    } else {
        ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE
    };
    let log_crc_pos = if cdb {
        ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_TRUE
    } else {
        ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_FALSE
    };
    let ghost new_ghost0: nat = arbitrary(); // TODO - replace with correct value
    let subregion = PersistentMemorySubregion::new(
        pm_region,
        log_metadata_pos,
        Ghost(LogMetadata::spec_size_of() + u64::spec_size_of()),
    );
    let log_metadata = match pm_region.read_aligned::<LogMetadata>(log_metadata_pos) {
        Ok(log_metadata) => log_metadata,
        Err(e) => {
            let ret = Err(LogErr::PmemErr { err: e });
            return ret;
        },
    };
    let log_crc = match pm_region.read_aligned::<u64>(log_crc_pos) {
        Ok(log_crc) => log_crc,
        Err(e) => {
            let ret = Err(LogErr::PmemErr { err: e });
            return ret;
        },
    };
    let ghost check_crc_ghost8: Seq<u8> = arbitrary(); // TODO - replace with correct value
    let ghost check_crc_ghost9: bool = arbitrary(); // TODO - replace with correct value
    let ghost check_crc_ghost10: Seq<int> = arbitrary(); // TODO - replace with correct value
    let ghost check_crc_ghost11: Seq<int> = arbitrary(); // TODO - replace with correct value
    if !check_crc(
        log_metadata.as_slice(),
        log_crc.as_slice(),
        Ghost(check_crc_ghost8),
        Ghost(check_crc_ghost9),
        Ghost(check_crc_ghost10),
        Ghost(check_crc_ghost11),
    ) {
        let ret = Err(LogErr::CRCMismatch);
        return ret;
    }
    let ghost extract_init_val_ghost6: LogMetadata = arbitrary(); // TODO - replace with correct value
    let ghost extract_init_val_ghost7: Seq<u8> = arbitrary(); // TODO - replace with correct value
    let ghost extract_init_val_ghost8: bool = arbitrary(); // TODO - replace with correct value
    let log_metadata = log_metadata.extract_init_val(
        Ghost(extract_init_val_ghost6),
        Ghost(extract_init_val_ghost7),
        Ghost(extract_init_val_ghost8),
    );
    let head = log_metadata.head;
    let log_length = log_metadata.log_length;
    if log_length > region_metadata.log_area_len {
        let ret = Err(LogErr::StartFailedDueToInvalidMemoryContents);
        return ret;
    }
    if log_length as u128 > u128::MAX - head {
        let ret = Err(LogErr::StartFailedDueToInvalidMemoryContents);
        return ret;
    }
    let head_log_area_offset: u64 = (head % region_metadata.log_area_len as u128) as u64;
    let ret =Ok(
        LogInfo {
            log_area_len: region_metadata.log_area_len,
            head,
            head_log_area_offset,
            log_length,
            log_plus_pending_length: log_length,
        },
    );
    ret
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
