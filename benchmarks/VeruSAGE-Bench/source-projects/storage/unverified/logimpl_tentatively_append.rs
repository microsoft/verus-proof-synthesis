use deps_hack::{pmsized_primitive, PmSized};
use vstd::prelude::*;
verus! {

pub open spec fn no_outstanding_writes_to_metadata(
    pm_region_view: PersistentMemoryRegionView,
) -> bool {
    pm_region_view.no_outstanding_writes_in_range(
        ABSOLUTE_POS_OF_GLOBAL_METADATA as int,
        ABSOLUTE_POS_OF_LOG_AREA as int,
    )
}

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

pub open spec fn log_area_offset_unreachable_during_recovery(
    head_log_area_offset: int,
    log_area_len: int,
    log_length: int,
    log_area_offset: int,
) -> bool {
    log_area_offset_to_relative_log_pos(log_area_offset, head_log_area_offset, log_area_len)
        >= log_length
}

#[verifier::external_body]
pub proof fn lemma_if_view_differs_only_in_log_area_parts_not_accessed_by_recovery_then_recover_state_matches(
    v1: PersistentMemoryRegionView,
    v2: PersistentMemoryRegionView,
    crash_state: Seq<u8>,
    log_id: u128,
    cdb: bool,
    info: LogInfo,
    state: AbstractLogState,
    is_writable_absolute_addr: spec_fn(int) -> bool,
)
    requires
        no_outstanding_writes_to_metadata(v1),
        memory_matches_deserialized_cdb(v1, cdb),
        metadata_consistent_with_info(v1, log_id, cdb, info),
        info_consistent_with_log_area_in_region(v1, info, state),
        ABSOLUTE_POS_OF_LOG_AREA + info.log_area_len <= v1.len(),
        v2.can_crash_as(crash_state),
        v1.len() == v2.len(),
        forall|addr: int| #[trigger]
            is_writable_absolute_addr(addr) <==> log_area_offset_unreachable_during_recovery(
                info.head_log_area_offset as int,
                info.log_area_len as int,
                info.log_length as int,
                addr - ABSOLUTE_POS_OF_LOG_AREA,
            ),
        views_differ_only_where_subregion_allows(
            v1,
            v2,
            ABSOLUTE_POS_OF_LOG_AREA as nat,
            info.log_area_len as nat,
            is_writable_absolute_addr,
        ),
    ensures
        v1.can_crash_as(v1.committed()),
        recover_state(crash_state, log_id) == recover_state(v1.committed(), log_id),
{
    unimplemented!()
}

#[verifier::external_body]
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
    unimplemented!()
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

#[verifier::external_body]
pub proof fn lemma_header_bytes_equal_implies_active_metadata_bytes_equal(
    mem1: Seq<u8>,
    mem2: Seq<u8>,
)
    requires
        ABSOLUTE_POS_OF_LOG_AREA <= mem1.len(),
        ABSOLUTE_POS_OF_LOG_AREA <= mem2.len(),
        mem1.subrange(ABSOLUTE_POS_OF_GLOBAL_METADATA as int, ABSOLUTE_POS_OF_LOG_AREA as int)
            =~= mem2.subrange(
            ABSOLUTE_POS_OF_GLOBAL_METADATA as int,
            ABSOLUTE_POS_OF_LOG_AREA as int,
        ),
        deserialize_and_check_log_cdb(mem1) is Some,
    ensures
        active_metadata_bytes_are_equal(mem1, mem2),
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

pub open spec fn log_area_offset_to_relative_log_pos(
    log_area_offset: int,
    head_log_area_offset: int,
    log_area_len: int,
) -> int {
    if log_area_offset >= head_log_area_offset {
        log_area_offset - head_log_area_offset
    } else {
        log_area_offset - head_log_area_offset + log_area_len
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

pub open spec fn recover_cdb(mem: Seq<u8>) -> Option<bool> {
    if mem.len() < ABSOLUTE_POS_OF_REGION_METADATA {
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
                if mem.len() < ABSOLUTE_POS_OF_LOG_CDB + u64::spec_size_of() {
                    None
                } else {
                    deserialize_and_check_log_cdb(mem)
                }
            } else {
                None
            }
        }
    }
}

pub open spec fn recover_state(mem: Seq<u8>, log_id: u128) -> Option<AbstractLogState> {
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

impl LogInfo {
    pub open spec fn tentatively_append(self, num_bytes: u64) -> Self {
        Self { log_plus_pending_length: (self.log_plus_pending_length + num_bytes) as u64, ..self }
    }
}

pub struct UntrustedLogImpl {
    cdb: bool,
    info: LogInfo,
    state: Ghost<AbstractLogState>,
}

impl UntrustedLogImpl {
    pub closed spec fn recover(mem: Seq<u8>, log_id: u128) -> Option<AbstractLogState> {
        if !metadata_types_set(mem) {
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
        &&& wrpm_region.inv()
        &&& no_outstanding_writes_to_metadata(wrpm_region@)
        &&& memory_matches_deserialized_cdb(wrpm_region@, self.cdb)
        &&& metadata_consistent_with_info(wrpm_region@, log_id, self.cdb, self.info)
        &&& info_consistent_with_log_area_in_region(wrpm_region@, self.info, self.state@)
        &&& can_only_crash_as_state(wrpm_region@, log_id, self.state@.drop_pending_appends())
        &&& metadata_types_set(wrpm_region@.committed())
    }

    pub closed spec fn view(&self) -> AbstractLogState {
        self.state@
    }

    #[verifier::external_body]
    exec fn tentatively_append_to_log<PMRegion>(
        &self,
        wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<TrustedPermission, PMRegion>,
        subregion: &WriteRestrictedPersistentMemorySubregion,
        bytes_to_append: &[u8],
        Tracked(perm): Tracked<&TrustedPermission>,
    ) -> (result: Result<u128, LogErr>) where PMRegion: PersistentMemoryRegion
        requires
            bytes_to_append.len() <= self.info.log_area_len - self.info.log_plus_pending_length,
            self.info.head + self.info.log_plus_pending_length + bytes_to_append.len() <= u128::MAX,
            subregion.inv(&*old(wrpm_region), perm),
            subregion.start() == ABSOLUTE_POS_OF_LOG_AREA,
            subregion.len() == self.info.log_area_len,
            info_consistent_with_log_area(
                subregion.view(&*old(wrpm_region)),
                self.info,
                self.state@,
            ),
            forall|log_area_offset: int| #[trigger]
                subregion.is_writable_relative_addr(log_area_offset)
                    <==> log_area_offset_unreachable_during_recovery(
                    self.info.head_log_area_offset as int,
                    self.info.log_area_len as int,
                    self.info.log_length as int,
                    log_area_offset,
                ),
        ensures
            subregion.inv(wrpm_region, perm),
            match result {
                Ok(offset) => {
                    &&& offset == self.info.head + self.info.log_plus_pending_length
                    &&& info_consistent_with_log_area(
                        subregion.view(wrpm_region),
                        self.info.tentatively_append(bytes_to_append.len() as u64),
                        self.state@.tentatively_append(bytes_to_append@),
                    )
                },
                Err(LogErr::InsufficientSpaceForAppend { available_space }) => {
                    &&& subregion.view(wrpm_region) == subregion.view(&*old(wrpm_region))
                    &&& available_space < bytes_to_append@.len()
                    &&& {
                        ||| available_space == self@.capacity - self@.log.len()
                            - self@.pending.len()
                        ||| available_space == u128::MAX - self@.head - self@.log.len()
                            - self@.pending.len()
                    }
                },
                _ => false,
            },
    {
        unimplemented!()
    }

    #[verifier::auto_ext_equal(assert, assert_by, ensures)]
    pub exec fn tentatively_append<PMRegion>(
        &mut self,
        wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<TrustedPermission, PMRegion>,
        bytes_to_append: &[u8],
        Ghost(log_id): Ghost<u128>,
        Tracked(perm): Tracked<&TrustedPermission>,
    ) -> (result: Result<u128, LogErr>) where PMRegion: PersistentMemoryRegion
        requires
            old(self).inv(&*old(wrpm_region), log_id),
            forall|s| #[trigger]
                perm.check_permission(s) <==> Self::recover(s, log_id) == Some(
                    old(self)@.drop_pending_appends(),
                ),
        ensures
            self.inv(wrpm_region, log_id),
            wrpm_region.constants() == old(wrpm_region).constants(),
            can_only_crash_as_state(wrpm_region@, log_id, self@.drop_pending_appends()),
            match result {
                Ok(offset) => {
                    let state = old(self)@;
                    &&& offset == state.head + state.log.len() + state.pending.len()
                    &&& self@ == old(self)@.tentatively_append(bytes_to_append@)
                },
                Err(LogErr::InsufficientSpaceForAppend { available_space }) => {
                    &&& self@ == old(self)@
                    &&& available_space < bytes_to_append@.len()
                    &&& {
                        ||| available_space == self@.capacity - self@.log.len()
                            - self@.pending.len()
                        ||| available_space == u128::MAX - self@.head - self@.log.len()
                            - self@.pending.len()
                    }
                },
                _ => false,
            },
    {
        let info = &self.info;
        let available_space: u64 = info.log_area_len - info.log_plus_pending_length as u64;
        let num_bytes: u64 = bytes_to_append.len() as u64;
        if num_bytes > available_space {
            let ret = Err(LogErr::InsufficientSpaceForAppend { available_space });
            return ret;
        }
        if num_bytes as u128 > u128::MAX - info.log_plus_pending_length as u128 - info.head {
            let ret = Err(
                LogErr::InsufficientSpaceForAppend {
                    available_space: (u128::MAX - info.log_plus_pending_length as u128
                        - info.head) as u64,
                },
            );
            return ret;
        }
        let tracked new_tracked0: &TrustedPermission = proof_from_false(); // TODO - replace with correct value
        let ghost new_ghost0: nat = arbitrary(); // TODO - replace with correct value
        let ghost new_ghost1: spec_fn(int) -> bool = arbitrary(); // TODO - replace with correct value
        let subregion = WriteRestrictedPersistentMemorySubregion::new(
            wrpm_region,
            Tracked(new_tracked0),
            ABSOLUTE_POS_OF_LOG_AREA,
            Ghost(new_ghost0),
            Ghost(new_ghost1),
        );
        let tracked tentatively_append_to_log_tracked0: &TrustedPermission = proof_from_false(); // TODO - replace with correct value
        let result = self.tentatively_append_to_log(
            wrpm_region,
            &subregion,
            bytes_to_append,
            Tracked(tentatively_append_to_log_tracked0),
        );
        let num_bytes: u64 = bytes_to_append.len() as u64;
        self.info.log_plus_pending_length = (self.info.log_plus_pending_length + num_bytes) as u64;
        let ghost state_ghost: AbstractLogState = arbitrary(); // TODO - replace with correct value
        self.state = Ghost(state_ghost);
        result
    }
}

pub struct AbstractLogState {
    pub head: int,
    pub log: Seq<u8>,
    pub pending: Seq<u8>,
    pub capacity: int,
}

impl AbstractLogState {
    pub open spec fn tentatively_append(self, bytes: Seq<u8>) -> Self {
        Self { pending: self.pending + bytes, ..self }
    }

    pub open spec fn drop_pending_appends(self) -> Self {
        Self { pending: Seq::<u8>::empty(), ..self }
    }
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

pub enum PmemError {
    InvalidFileName,
    CannotOpenPmFile,
    NotPm,
    PmdkError,
    AccessOutOfRange,
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

pub struct PersistentMemoryConstants {
    pub impervious_to_corruption: bool,
}

pub trait PersistentMemoryRegion: Sized {

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
    #[verifier::external_body]
    pub exec fn new<Perm, PMRegion>(
        wrpm: &WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        Tracked(perm): Tracked<&Perm>,
        start: u64,
        Ghost(len): Ghost<nat>,
        Ghost(is_writable_absolute_addr_fn): Ghost<spec_fn(int) -> bool>,
    ) -> (result: Self) where Perm: CheckPermission<Seq<u8>>, PMRegion: PersistentMemoryRegion
        requires
            wrpm.inv(),
            0 <= len,
            start + len <= wrpm@.len() <= u64::MAX,
            forall|alt_region_view: PersistentMemoryRegionView, alt_crash_state: Seq<u8>|
                {
                    &&& #[trigger] alt_region_view.can_crash_as(alt_crash_state)
                    &&& wrpm@.len() == alt_region_view.len()
                    &&& views_differ_only_where_subregion_allows(
                        wrpm@,
                        alt_region_view,
                        start as nat,
                        len,
                        is_writable_absolute_addr_fn,
                    )
                } ==> perm.check_permission(alt_crash_state),
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

    pub open spec fn is_writable_relative_addr(self, addr: int) -> bool {
        self.is_writable_absolute_addr_fn()(addr + self.start())
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

pub trait CheckPermission<State> {
    spec fn check_permission(&self, state: State) -> bool;
}

#[allow(dead_code)]
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
