use vstd::prelude::*;
use deps_hack::{PmSized, pmsized_primitive};

verus! {
    pub fn main()
    {
    }

    /*log\inv_v*/
    pub open spec fn no_outstanding_writes_to_metadata(
        pm_region_view: PersistentMemoryRegionView,
    ) -> bool
    {
        pm_region_view.no_outstanding_writes_in_range(ABSOLUTE_POS_OF_GLOBAL_METADATA as int,
                                                      ABSOLUTE_POS_OF_LOG_AREA as int)
    }

    pub open spec fn memory_matches_deserialized_cdb(pm_region_view: PersistentMemoryRegionView, cdb: bool) -> bool
    {
        &&& pm_region_view.no_outstanding_writes_in_range(ABSOLUTE_POS_OF_LOG_CDB as int,
                                                        ABSOLUTE_POS_OF_LOG_CDB + u64::spec_size_of())
        &&& deserialize_and_check_log_cdb(pm_region_view.committed()) == Some(cdb)
    }

    pub open spec fn metadata_consistent_with_info(
        pm_region_view: PersistentMemoryRegionView,
        log_id: u128,
        cdb: bool,
        info: LogInfo,
    ) -> bool
    {
        let mem = pm_region_view.committed();
        let global_metadata = deserialize_global_metadata(mem);
        let global_crc = deserialize_global_crc(mem);
        let region_metadata = deserialize_region_metadata(mem);
        let region_crc = deserialize_region_crc(mem);
        let log_metadata = deserialize_log_metadata(mem, cdb);
        let log_crc = deserialize_log_crc(mem, cdb);

        // No outstanding writes to global metadata, region metadata, or the log metadata CDB
        &&& pm_region_view.no_outstanding_writes_in_range(ABSOLUTE_POS_OF_GLOBAL_METADATA as int,
                                                        ABSOLUTE_POS_OF_LOG_CDB as int)
        // Also, no outstanding writes to the log metadata corresponding to the active log metadata CDB
        &&& pm_region_view.no_outstanding_writes_in_range(get_log_metadata_pos(cdb) as int,
                                                        get_log_crc_end(cdb) as int)

        // All the CRCs match
        &&& global_crc == global_metadata.spec_crc()
        &&& region_crc == region_metadata.spec_crc()
        &&& log_crc == log_metadata.spec_crc()

        // Various fields are valid and match the parameters to this function
        &&& global_metadata.program_guid == LOG_PROGRAM_GUID
        &&& global_metadata.version_number == LOG_PROGRAM_VERSION_NUMBER
        &&& global_metadata.length_of_region_metadata == RegionMetadata::spec_size_of()
        &&& region_metadata.region_size == mem.len()
        &&& region_metadata.log_id == log_id
        &&& region_metadata.log_area_len == info.log_area_len
        &&& log_metadata.head == info.head
        &&& log_metadata.log_length == info.log_length

        // The memory region is large enough to hold the entirety of the log area
        &&& mem.len() >= ABSOLUTE_POS_OF_LOG_AREA + info.log_area_len
    }

    pub open spec fn info_consistent_with_log_area(
        log_area_view: PersistentMemoryRegionView,
        info: LogInfo,
        state: AbstractLogState,
    ) -> bool
    {
        // `info` satisfies certain invariant properties
        &&& info.log_area_len >= MIN_LOG_AREA_SIZE
        &&& info.log_length <= info.log_plus_pending_length <= info.log_area_len
        &&& info.head_log_area_offset == info.head as int % info.log_area_len as int
        &&& info.head + info.log_plus_pending_length <= u128::MAX

        // `info` and `state` are consistent with each other
        &&& state.log.len() == info.log_length
        &&& state.pending.len() == info.log_plus_pending_length - info.log_length
        &&& state.head == info.head
        &&& state.capacity == info.log_area_len

        // The log area is consistent with `info` and `state`
        &&& forall |pos_relative_to_head: int| {
                let log_area_offset =
                    #[trigger] relative_log_pos_to_log_area_offset(pos_relative_to_head,
                                                                   info.head_log_area_offset as int,
                                                                   info.log_area_len as int);
                let pmb = log_area_view.state[log_area_offset];
                &&& 0 <= pos_relative_to_head < info.log_length ==> {
                      &&& pmb.state_at_last_flush == state.log[pos_relative_to_head]
                      &&& pmb.outstanding_write.is_none()
                   }
                &&& info.log_length <= pos_relative_to_head < info.log_plus_pending_length ==>
                       pmb.flush_byte() == state.pending[pos_relative_to_head - info.log_length]
                &&& info.log_plus_pending_length <= pos_relative_to_head < info.log_area_len ==>
                       pmb.outstanding_write.is_none()
            }
    }

    pub open spec fn info_consistent_with_log_area_in_region(
        pm_region_view: PersistentMemoryRegionView,
        info: LogInfo,
        state: AbstractLogState,
    ) -> bool
    {
        &&& pm_region_view.len() >= ABSOLUTE_POS_OF_LOG_AREA + info.log_area_len
        &&& info_consistent_with_log_area(
               get_subregion_view(pm_region_view, ABSOLUTE_POS_OF_LOG_AREA as nat, info.log_area_len as nat),
               info,
               state
           )
    }

    pub open spec fn metadata_types_set(mem: Seq<u8>) -> bool 
    {
        &&& {
            let metadata_pos = ABSOLUTE_POS_OF_GLOBAL_METADATA as int;
            let crc_pos = ABSOLUTE_POS_OF_GLOBAL_CRC as int;
            let metadata = GlobalMetadata::spec_from_bytes(extract_bytes(mem, metadata_pos as nat,
                                                                         GlobalMetadata::spec_size_of()));
            let crc = u64::spec_from_bytes(extract_bytes(mem, crc_pos as nat, u64::spec_size_of()));
            &&& GlobalMetadata::bytes_parseable(extract_bytes(mem, metadata_pos as nat, GlobalMetadata::spec_size_of()))
            &&& u64::bytes_parseable(extract_bytes(mem, crc_pos as nat, u64::spec_size_of()))
            &&& crc == spec_crc_u64(metadata.spec_to_bytes())
        }
        &&& {
            let metadata_pos = ABSOLUTE_POS_OF_REGION_METADATA as int;
            let crc_pos = ABSOLUTE_POS_OF_REGION_CRC as int;
            let metadata = RegionMetadata::spec_from_bytes(extract_bytes(mem, metadata_pos as nat,
                                                                         RegionMetadata::spec_size_of()));
            let crc = u64::spec_from_bytes(extract_bytes(mem, crc_pos as nat, u64::spec_size_of()));
            &&& RegionMetadata::bytes_parseable(extract_bytes(mem, metadata_pos as nat, RegionMetadata::spec_size_of()))
            &&& u64::bytes_parseable(extract_bytes(mem, crc_pos as nat, u64::spec_size_of()))
            &&& crc == spec_crc_u64(metadata.spec_to_bytes())
        }
        &&& {
            let cdb_pos = ABSOLUTE_POS_OF_LOG_CDB as int;
            let cdb = u64::spec_from_bytes(extract_bytes(mem, cdb_pos as nat, u64::spec_size_of()));
            let metadata_pos = if cdb == CDB_TRUE { ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_TRUE }
                               else { ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE };
            let metadata = LogMetadata::spec_from_bytes(extract_bytes(mem, metadata_pos as nat, LogMetadata::spec_size_of()));
            let crc_pos = if cdb == CDB_TRUE { ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_TRUE }
                          else { ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_FALSE };
            let crc = u64::spec_from_bytes(extract_bytes(mem, crc_pos as nat, u64::spec_size_of()));
            &&& u64::bytes_parseable(extract_bytes(mem, cdb_pos as nat, u64::spec_size_of()))
            &&& cdb == CDB_TRUE || cdb == CDB_FALSE 
            &&& LogMetadata::bytes_parseable(extract_bytes(mem, metadata_pos as nat, LogMetadata::spec_size_of()))
            &&& u64::bytes_parseable(extract_bytes(mem, crc_pos as nat, u64::spec_size_of()))
            &&& crc == spec_crc_u64(metadata.spec_to_bytes())
        }
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

    impl PmCopy for GlobalMetadata {}

    #[repr(C)]
    #[derive(PmSized, Copy, Clone, Default)]

    pub struct RegionMetadata {
        pub region_size: u64,
        pub log_area_len: u64,
        pub log_id: u128,
    }

    impl PmCopy for RegionMetadata {}

    #[repr(C)]
    #[derive(PmSized, Copy, Clone, Default)]

    pub struct LogMetadata {
        pub log_length: u64,
        pub _padding: u64,
        pub head: u128,
    }

    impl PmCopy for LogMetadata {}

    pub open spec fn extract_global_metadata(mem: Seq<u8>) -> Seq<u8>
    {
        extract_bytes(mem, ABSOLUTE_POS_OF_GLOBAL_METADATA as nat, GlobalMetadata::spec_size_of() as nat)
    }

    pub open spec fn deserialize_global_metadata(mem: Seq<u8>) -> GlobalMetadata
    {
        let bytes = extract_global_metadata(mem);
        GlobalMetadata::spec_from_bytes(bytes)
    }

    pub open spec fn extract_global_crc(mem: Seq<u8>) -> Seq<u8>
    {
        extract_bytes(mem, ABSOLUTE_POS_OF_GLOBAL_CRC as nat, u64::spec_size_of() as nat)
    }

    pub open spec fn deserialize_global_crc(mem: Seq<u8>) -> u64
    {
        let bytes = extract_global_crc(mem);
        u64::spec_from_bytes(bytes)
    }

    pub open spec fn extract_region_metadata(mem: Seq<u8>) -> Seq<u8>
    {
        extract_bytes(mem, ABSOLUTE_POS_OF_REGION_METADATA as nat, RegionMetadata::spec_size_of() as nat)
    }

    pub open spec fn deserialize_region_metadata(mem: Seq<u8>) -> RegionMetadata
    {
        let bytes = extract_region_metadata(mem);
        RegionMetadata::spec_from_bytes(bytes)
    }

    pub open spec fn extract_region_crc(mem: Seq<u8>) -> Seq<u8>
    {
        extract_bytes(mem, ABSOLUTE_POS_OF_REGION_CRC as nat, u64::spec_size_of() as nat)
    }

    pub open spec fn deserialize_region_crc(mem: Seq<u8>) -> u64
    {
        let bytes = extract_region_crc(mem);
        u64::spec_from_bytes(bytes)
    }

    pub open spec fn extract_log_cdb(mem: Seq<u8>) -> Seq<u8>
    {
        extract_bytes(mem, ABSOLUTE_POS_OF_LOG_CDB as nat, u64::spec_size_of() as nat)
    }

    pub open spec fn deserialize_log_cdb(mem: Seq<u8>) -> u64
    {
        let bytes = extract_log_cdb(mem);
        u64::spec_from_bytes(bytes)
    }

    pub open spec fn deserialize_and_check_log_cdb(mem: Seq<u8>) -> Option<bool>
    {
        let log_cdb = deserialize_log_cdb(mem);
        if log_cdb == CDB_FALSE {
            Some(false)
        } else if log_cdb == CDB_TRUE {
            Some(true)
        } else {
            None
        }
    }

    pub open spec fn get_log_metadata_pos(cdb: bool) -> u64
    {
        if cdb { ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_TRUE } else { ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE }
    }

    pub open spec fn get_log_crc_end(cdb: bool) -> u64
    {
        (get_log_metadata_pos(cdb) + LogMetadata::spec_size_of() + u64::spec_size_of()) as u64
    }

    pub open spec fn extract_log_metadata(mem: Seq<u8>, cdb: bool) -> Seq<u8>
    {
        let pos = get_log_metadata_pos(cdb);
        extract_bytes(mem, pos as nat, LogMetadata::spec_size_of() as nat)
    }

    pub open spec fn deserialize_log_metadata(mem: Seq<u8>, cdb: bool) -> LogMetadata
    {
        let bytes = extract_log_metadata(mem, cdb);
        LogMetadata::spec_from_bytes(bytes)
    }

    pub open spec fn extract_log_crc(mem: Seq<u8>, cdb: bool) -> Seq<u8>
    {
        let pos = if cdb { ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_TRUE }
                  else { ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_FALSE };
        extract_bytes(mem, pos as nat, u64::spec_size_of() as nat)
    }

    pub open spec fn deserialize_log_crc(mem: Seq<u8>, cdb: bool) -> u64
    {
        let bytes = extract_log_crc(mem, cdb);
        u64::spec_from_bytes(bytes)
    }

    pub open spec fn relative_log_pos_to_log_area_offset(
        pos_relative_to_head: int,
        head_log_area_offset: int,
        log_area_len: int
    ) -> int
    {
        let log_area_offset = head_log_area_offset + pos_relative_to_head;
        if log_area_offset >= log_area_len {
            log_area_offset - log_area_len
        }
        else {
            log_area_offset
        }
    }

    pub open spec fn extract_log_from_log_area(log_area: Seq<u8>, head: int, log_length: int) -> Seq<u8>
    {
        let head_log_area_offset = head % (log_area.len() as int);
        Seq::<u8>::new(log_length as nat, |pos_relative_to_head: int|
                       log_area[relative_log_pos_to_log_area_offset(pos_relative_to_head, head_log_area_offset,
                                                                    log_area.len() as int)])
    }

    pub open spec fn recover_log_from_log_area_given_metadata(
        log_area: Seq<u8>,
        head: int,
        log_length: int,
    ) -> Option<AbstractLogState>
    {
        if log_length > log_area.len() || head + log_length > u128::MAX
        {
            None
        }
        else {
            Some(AbstractLogState {
                head,
                log: extract_log_from_log_area(log_area, head, log_length),
                pending: Seq::<u8>::empty(),
                capacity: log_area.len() as int
            })
        }
    }

    pub open spec fn recover_log(
        mem: Seq<u8>,
        log_area_len: int,
        head: int,
        log_length: int,
    ) -> Option<AbstractLogState>
    {
        recover_log_from_log_area_given_metadata(
            extract_bytes(mem, ABSOLUTE_POS_OF_LOG_AREA as nat, log_area_len as nat), head, log_length
        )
    }

    pub open spec fn recover_given_cdb(
        mem: Seq<u8>,
        log_id: u128,
        cdb: bool
    ) -> Option<AbstractLogState>
    {
        if mem.len() < ABSOLUTE_POS_OF_LOG_AREA + MIN_LOG_AREA_SIZE {
            // To be valid, the memory's length has to be big enough to store at least
            // `MIN_LOG_AREA_SIZE` in the log area.
            None
        }
        else {
            let global_metadata = deserialize_global_metadata(mem);
            let global_crc = deserialize_global_crc(mem);
            if global_crc != global_metadata.spec_crc() {
                // To be valid, the global metadata CRC has to be a valid CRC of the global metadata
                // encoded as bytes.
                None
            }
            else {
                if global_metadata.program_guid != LOG_PROGRAM_GUID {
                    // To be valid, the global metadata has to refer to this program's GUID.
                    // Otherwise, it wasn't created by this program.
                    None
                }
                else if global_metadata.version_number == 1 {
                    // If this metadata was written by version #1 of this code, then this is how to
                    // interpret it:

                    if global_metadata.length_of_region_metadata != RegionMetadata::spec_size_of() {
                        // To be valid, the global metadata's encoding of the region metadata's
                        // length has to be what we expect. (This version of the code doesn't
                        // support any other length of region metadata.)
                        None
                    }
                    else {
                        let region_metadata = deserialize_region_metadata(mem);
                        let region_crc = deserialize_region_crc(mem);
                        if region_crc != region_metadata.spec_crc() {
                            // To be valid, the region metadata CRC has to be a valid CRC of the region
                            // metadata encoded as bytes.
                            None
                        }
                        else {
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
                            }
                            else {
                                let log_metadata = deserialize_log_metadata(mem, cdb);
                                let log_crc = deserialize_log_crc(mem, cdb);
                                if log_crc != log_metadata.spec_crc() {
                                    // To be valid, the log metadata CRC has to be a valid CRC of the
                                    // log metadata encoded as bytes. (This only applies to the
                                    // "active" log metadata, i.e., the log metadata
                                    // corresponding to the current CDB.)
                                    None
                                }
                                else {
                                    recover_log(mem, region_metadata.log_area_len as int, log_metadata.head as int,
                                                log_metadata.log_length as int)
                                }
                            }
                        }
                    }
                }
                else {
                    // This version of the code doesn't know how to parse metadata for any other
                    // versions of this code besides 1. If we reach this point, we're presumably
                    // reading metadata written by a future version of this code, which we can't
                    // interpret.
                    None
                }
            }
        }
    }

    pub open spec fn recover_cdb(mem: Seq<u8>) -> Option<bool>
    {
        if mem.len() < ABSOLUTE_POS_OF_REGION_METADATA {
            // If there isn't space in memory to store the global metadata
            // and CRC, then this region clearly isn't a valid log region.
            None
        }
        else {
            let global_metadata = deserialize_global_metadata(mem);
            let global_crc = deserialize_global_crc(mem);
            if global_crc != global_metadata.spec_crc() {
                // To be valid, the global metadata CRC has to be a valid CRC of the global metadata
                // encoded as bytes.
                None
            }
            else {
                if global_metadata.program_guid != LOG_PROGRAM_GUID {
                    // To be valid, the global metadata has to refer to this program's GUID.
                    // Otherwise, it wasn't created by this program.
                    None
                }
                else if global_metadata.version_number == 1 {
                    // If this metadata was written by version #1 of this code, then this is how to
                    // interpret it:

                    if mem.len() < ABSOLUTE_POS_OF_LOG_CDB + u64::spec_size_of() {
                        // If memory isn't big enough to store the CDB, then this region isn't
                        // valid.
                        None
                    }
                    else {
                        // Extract and parse the log metadata CDB
                        deserialize_and_check_log_cdb(mem)
                    }
                }
                else {
                    // This version of the code doesn't know how to parse metadata for any other
                    // versions of this code besides 1. If we reach this point, we're presumably
                    // reading metadata written by a future version of this code, which we can't
                    // interpret.
                    None
                }
            }
        }
    }

    pub open spec fn recover_state(mem: Seq<u8>, log_id: u128) -> Option<AbstractLogState>
    {
        // To recover, first recover the CDB, then use it to recover the abstract state.
        match recover_cdb(mem) {
            Some(cdb) => recover_given_cdb(mem, log_id, cdb),
            None => None
        }
    }

    /*log\logimpl_t*/
    pub open spec fn read_correct_modulo_corruption(bytes: Seq<u8>, true_bytes: Seq<u8>,
                                                    impervious_to_corruption: bool) -> bool
    {
        if impervious_to_corruption {
            // If the region is impervious to corruption, the bytes read
            // must match the true bytes, i.e., the bytes last written.

            bytes == true_bytes
        }
        else {
            // Otherwise, there must exist a sequence of distinct
            // addresses `addrs` such that the nth byte of `bytes` is
            // a possibly corrupted version of the nth byte of
            // `true_bytes` read from the nth address in `addrs`.  We
            // don't require the sequence of addresses to be
            // contiguous because the data might not be contiguous on
            // disk (e.g., if it wrapped around the log area).

            exists |addrs: Seq<int>| {
                &&& all_elements_unique(addrs)
                &&& #[trigger] maybe_corrupted(bytes, true_bytes, addrs)
            }
        }
    }

    pub open spec fn can_only_crash_as_state(
        pm_region_view: PersistentMemoryRegionView,
        log_id: u128,
        state: AbstractLogState,
    ) -> bool
    {
        forall |s| #[trigger] pm_region_view.can_crash_as(s) ==>
            UntrustedLogImpl::recover(s, log_id) == Some(state)
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
        PmemErr { err: PmemError } // janky workaround so that callers can handle PmemErrors as LogErrors
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

    impl UntrustedLogImpl
    {
        pub closed spec fn recover(mem: Seq<u8>, log_id: u128) -> Option<AbstractLogState>
        {
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
        ) -> bool
            where
                Perm: CheckPermission<Seq<u8>>,
                PMRegion: PersistentMemoryRegion
        {
            &&& wrpm_region.inv() // whatever the persistent memory regions require as an invariant
            &&& no_outstanding_writes_to_metadata(wrpm_region@)
            &&& memory_matches_deserialized_cdb(wrpm_region@, self.cdb)
            &&& metadata_consistent_with_info(wrpm_region@, log_id, self.cdb, self.info)
            &&& info_consistent_with_log_area_in_region(wrpm_region@, self.info, self.state@)
            &&& can_only_crash_as_state(wrpm_region@, log_id, self.state@.drop_pending_appends())
            &&& metadata_types_set(wrpm_region@.committed())
        }

        pub closed spec fn view(&self) -> AbstractLogState
        {
            self.state@
        }

	#[verifier::external_body]
        proof fn lemma_read_of_continuous_range(
            &self,
            pm_region_view: PersistentMemoryRegionView,
            log_id: u128,
            pos: int,
            len: int,
            addr: int,
        )
            requires
                len > 0,
                metadata_consistent_with_info(pm_region_view, log_id, self.cdb, self.info),
                info_consistent_with_log_area_in_region(pm_region_view, self.info, self.state@),
                ({
                    let info = self.info;
                    let max_len_without_wrapping = info.log_area_len -
                        relative_log_pos_to_log_area_offset(pos - info.head,
                                                            info.head_log_area_offset as int,
                                                            info.log_area_len as int);
                    &&& pos >= info.head
                    &&& pos + len <= info.head + info.log_length
                    &&& len <= max_len_without_wrapping
                    &&& addr == ABSOLUTE_POS_OF_LOG_AREA +
                           relative_log_pos_to_log_area_offset(pos - info.head as int,
                                                               info.head_log_area_offset as int,
                                                               info.log_area_len as int)
                })
            ensures
                ({
                    let log = self@;
                    &&& pm_region_view.no_outstanding_writes_in_range(addr, addr + len)
                    &&& pm_region_view.committed().subrange(addr, addr + len)
                           == log.log.subrange(pos - log.head, pos + len - log.head)
                })
	{
		unimplemented!()
	}

        pub exec fn read<Perm, PMRegion>(
            &self,
            wrpm_region: &WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
            pos: u128,
            len: u64,
            Ghost(log_id): Ghost<u128>,
        ) -> (result: Result<(Vec<u8>, Ghost<Seq<int>>), LogErr>)
            where
                Perm: CheckPermission<Seq<u8>>,
                PMRegion: PersistentMemoryRegion,
            requires
                self.inv(wrpm_region, log_id),
                pos + len <= u128::MAX
            ensures
                ({
                    let log = self@;
                    match result {
                        Ok((bytes, addrs)) => {
                            let true_bytes = self@.read(pos as int, len as int);
                            &&& pos >= log.head
                            &&& pos + len <= log.head + log.log.len()
                            &&& read_correct_modulo_corruption(bytes@, true_bytes,
                                                              wrpm_region.constants().impervious_to_corruption)
                        },
                        Err(LogErr::CantReadBeforeHead{ head: head_pos }) => {
                            &&& pos < log.head
                            &&& head_pos == log.head
                        },
                        Err(LogErr::CantReadPastTail{ tail }) => {
                            &&& pos + len > log.head + log.log.len()
                            &&& tail == log.head + log.log.len()
                        },
                        _ => false,
                    }
                })
        {
            // Handle error cases due to improper parameters passed to the
            // function.

            let info = &self.info;
            if pos < info.head {
                return Err(LogErr::CantReadBeforeHead{ head: info.head })
            }
            if len > info.log_length { // We have to do this check first to avoid underflow in the next comparison
                return Err(LogErr::CantReadPastTail{ tail: info.head + info.log_length as u128 })
            }
            if pos - info.head > (info.log_length - len) as u128 { // we know `info.log_length - len` can't underflow
                return Err(LogErr::CantReadPastTail{ tail: info.head + info.log_length as u128 })
            }

            let ghost s = self.state@;
            let ghost true_bytes = s.log.subrange(pos - s.head, pos + len - s.head);

            if len == 0 {
                // Case 0: The trivial case where we're being asked to read zero bytes.

                assert (true_bytes =~= Seq::<u8>::empty());
                assert (maybe_corrupted(Seq::<u8>::empty(), true_bytes, Seq::<int>::empty()));
                return Ok((Vec::<u8>::new(), Ghost(Seq::empty())));
            }

            let pm_region = wrpm_region.get_pm_region_ref();

            let log_area_len: u64 = info.log_area_len;
            let relative_pos: u64 = (pos - info.head) as u64;
            if relative_pos >= log_area_len - info.head_log_area_offset {

                // Case 1: The position we're being asked to read appears
                // in the log area before the log head. So the read doesn't
                // need to wrap.
                //
                // We could compute the address to write to with:
                //
                // `write_addr = ABSOLUTE_POS_OF_LOG_AREA + pos % info.log_area_len;`
                //
                // But we can replace the expensive modulo operation above with two subtraction
                // operations as follows. This is somewhat subtle, but we have verification backing
                // us up and proving this optimization correct.

                let addr = ABSOLUTE_POS_OF_LOG_AREA + relative_pos - (info.log_area_len - info.head_log_area_offset);
                proof { self.lemma_read_of_continuous_range(pm_region@, log_id, pos as int,
                                                            len as int, addr as int); }
                let bytes = match pm_region.read_unaligned(addr, len) {
                    Ok(bytes) => bytes,
                    Err(e) => {
                        assert(e == PmemError::AccessOutOfRange);
                        return Err(LogErr::PmemErr{ err: e });
                    }
                };
                return Ok((bytes, Ghost(Seq::new(len as nat, |i: int| i + addr))));
            }

            // The log area wraps past the point we're reading from, so we
            // need to compute the maximum length we can read without
            // wrapping to be able to figure out whether we need to wrap.

            let max_len_without_wrapping: u64 = log_area_len - info.head_log_area_offset - relative_pos;
            assert(max_len_without_wrapping == info.log_area_len -
                   relative_log_pos_to_log_area_offset(pos - info.head,
                                                       info.head_log_area_offset as int, info.log_area_len as int));

            // Whether we need to wrap or not, we know the address where
            // our read should start, so we can compute that and put it in
            // `addr`.
            //
            // We could compute the address to write to with:
            //
            // `write_addr = ABSOLUTE_POS_OF_LOG_AREA + pos % info.log_area_len;`
            //
            // But we can replace the expensive modulo operation above with
            // one addition operation as follows. This is somewhat subtle,
            // but we have verification backing us up and proving this
            // optimization correct.

            let addr: u64 = ABSOLUTE_POS_OF_LOG_AREA + relative_pos + info.head_log_area_offset;
            assert(addr == ABSOLUTE_POS_OF_LOG_AREA +
                   relative_log_pos_to_log_area_offset(pos - info.head,
                                                       info.head_log_area_offset as int,
                                                       info.log_area_len as int));

            if len <= max_len_without_wrapping {

                // Case 2: We're reading few enough bytes that we don't have to wrap.

                proof { self.lemma_read_of_continuous_range(pm_region@, log_id, pos as int,
                                                            len as int, addr as int); }
                let bytes = match pm_region.read_unaligned(addr, len) {
                    Ok(bytes) => bytes,
                    Err(e) => {
                        assert(e == PmemError::AccessOutOfRange);
                        return Err(LogErr::PmemErr{ err: e });
                    }
                };
                return Ok((bytes, Ghost(Seq::new(len as nat, |i: int| i + addr))));
            }

            // Case 3: We're reading enough bytes that we have to wrap.
            // That necessitates doing two contiguous reads, one from the
            // end of the log area and one from the beginning, and
            // concatenating the results.

            proof {
                self.lemma_read_of_continuous_range(pm_region@, log_id, pos as int,
                                                    max_len_without_wrapping as int, addr as int);
            }

            let mut part1 = match pm_region.read_unaligned(addr, max_len_without_wrapping) {
                Ok(part1) => part1,
                Err(e) => {
                    assert(e == PmemError::AccessOutOfRange);
                    return Err(LogErr::PmemErr{ err: e });
                }
            };

            proof {
                self.lemma_read_of_continuous_range(pm_region@, log_id,
                                                    pos + max_len_without_wrapping,
                                                    len - max_len_without_wrapping,
                                                    ABSOLUTE_POS_OF_LOG_AREA as int);
            }

            let mut part2 = match pm_region.read_unaligned(ABSOLUTE_POS_OF_LOG_AREA, len - max_len_without_wrapping) {
                Ok(part2) => part2,
                Err(e) => {
                    assert(e == PmemError::AccessOutOfRange);
                    return Err(LogErr::PmemErr{ err: e });
                }
            };

            // Now, prove that concatenating them produces the correct
            // bytes to return. The subtle thing in this argument is that
            // the bytes are only correct modulo corruption. And the
            // "correct modulo corruption" specification function talks
            // about the concrete addresses the bytes were read from and
            // demands that those addresses all be distinct.

            proof {
                let true_part1 = s.log.subrange(pos - s.head, pos + max_len_without_wrapping - s.head);
                let true_part2 = s.log.subrange(pos + max_len_without_wrapping - s.head, pos + len - s.head);
                let addrs1 = Seq::<int>::new(max_len_without_wrapping as nat, |i: int| i + addr);
                let addrs2 = Seq::<int>::new((len - max_len_without_wrapping) as nat,
                                           |i: int| i + ABSOLUTE_POS_OF_LOG_AREA);
                assert(true_part1 + true_part2 =~= s.log.subrange(pos - s.head, pos + len - s.head));

                if !pm_region.constants().impervious_to_corruption {
                    assert(maybe_corrupted(part1@ + part2@, true_part1 + true_part2, addrs1 + addrs2));
                    assert(all_elements_unique(addrs1 + addrs2));
                }
            }

            // Append the two byte vectors together and return the result.

            part1.append(&mut part2);
            let addrs = Ghost(Seq::<int>::new(max_len_without_wrapping as nat, |i: int| i + addr) + 
                Seq::<int>::new((len - max_len_without_wrapping) as nat, |i: int| i + ABSOLUTE_POS_OF_LOG_AREA));
            Ok((part1, addrs))
        }
    }

    /*log\logspec_t*/

    pub struct AbstractLogState {
        pub head: int,
        pub log: Seq<u8>,
        pub pending: Seq<u8>,
        pub capacity: int,
    }

    impl AbstractLogState
    {

        pub open spec fn read(self, pos: int, len: int) -> Seq<u8>
        {
            self.log.subrange(pos - self.head, pos - self.head + len)
        }

        pub open spec fn drop_pending_appends(self) -> Self
        {
            Self { pending: Seq::<u8>::empty(), ..self }
        }
    }

    /*util_v*/
    pub open spec fn nat_seq_max(seq: Seq<nat>) -> nat 
        recommends 
            0 < seq.len(),
        decreases seq.len()
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
        axiom_to_from_bytes
    }

    pub trait PmCopy : PmSized + SpecPmSized + Sized + Copy {}

    // PmCopyHelper is a subtrait of PmCopy that exists to provide a blanket
    // implementation of these methods for all PmCopy objects. 
    pub trait PmCopyHelper : PmCopy {
 
        spec fn spec_to_bytes(self) -> Seq<u8>;

        spec fn spec_from_bytes(bytes: Seq<u8>) -> Self;

        spec fn bytes_parseable(bytes: Seq<u8>) -> bool;

        spec fn spec_crc(self) -> u64;
    }

    impl<T> PmCopyHelper for T where T: PmCopy {
        closed spec fn spec_to_bytes(self) -> Seq<u8>;

	#[verifier::external_body]
        closed spec fn spec_from_bytes(bytes: Seq<u8>) -> Self
	{
		unimplemented!()
	}

        open spec fn spec_crc(self) -> u64 {
            spec_crc_u64(self.spec_to_bytes())
        }

        open spec fn bytes_parseable(bytes: Seq<u8>) -> bool
        {
            Self::spec_from_bytes(bytes).spec_to_bytes() == bytes
        }
    }

	#[verifier::external_body]
    pub broadcast proof fn axiom_bytes_len<S: PmCopy>(s: S)
        ensures 
            #[trigger] s.spec_to_bytes().len() == S::spec_size_of()
	{
		unimplemented!()
	}

	#[verifier::external_body]
    pub broadcast proof fn axiom_to_from_bytes<S: PmCopy>(s: S)
        ensures 
            s == #[trigger] S::spec_from_bytes(s.spec_to_bytes())
	{
		unimplemented!()
	}

    impl PmCopy for u64 {}

    global size_of usize == 8;

    global size_of isize == 8;

    pub trait SpecPmSized : UnsafeSpecPmSized {

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
        open spec fn spec_size_of() -> nat
        {
            (N * T::spec_size_of()) as nat
        }   

        open spec fn spec_align_of() -> nat
        {
            T::spec_align_of()
        }
    }

	#[verifier::external_body]
    pub open spec fn spec_padding_needed(offset: nat, align: nat) -> nat
	{
		unimplemented!()
	}

    #[verifier::external_body]
    pub const fn padding_needed(offset: usize, align: usize) -> (out: usize) 
        requires 
            align > 0,
        ensures 
            out <= align,
            out as nat == spec_padding_needed(offset as nat, align as nat)
    {
        unimplemented!()
    }
 


    /*pmem\pmemspec_t*/
    pub enum PmemError {
        InvalidFileName,
        CannotOpenPmFile,
        NotPm,
        PmdkError,
        AccessOutOfRange,
    }

    pub closed spec fn maybe_corrupted_byte(byte: u8, true_byte: u8, addr: int) -> bool;

    pub open spec fn all_elements_unique(seq: Seq<int>) -> bool {
        forall |i: int, j: int| 0 <= i < j < seq.len() ==> seq[i] != seq[j]
    }

    pub open spec fn maybe_corrupted(bytes: Seq<u8>, true_bytes: Seq<u8>, addrs: Seq<int>) -> bool {
        &&& bytes.len() == true_bytes.len() == addrs.len()
        &&& forall |i: int| #![auto] 0 <= i < bytes.len() ==> maybe_corrupted_byte(bytes[i], true_bytes[i], addrs[i])
    }

    pub closed spec fn spec_crc_u64(bytes: Seq<u8>) -> u64;

    pub const CDB_FALSE: u64 = 0xa32842d19001605e; // CRC(b"0")

    pub const CDB_TRUE: u64  = 0xab21aa73069531b7; // CRC(b"1")

    pub open spec fn const_persistence_chunk_size() -> int { 8 }

    pub struct PersistentMemoryByte {
        pub state_at_last_flush: u8,
        pub outstanding_write: Option<u8>,
    }


    impl PersistentMemoryByte
    {
        pub open spec fn flush_byte(self) -> u8
        {
            match self.outstanding_write {
                None => self.state_at_last_flush,
                Some(b) => b
            }
        }
    }

    pub struct PersistentMemoryRegionView
    {
        pub state: Seq<PersistentMemoryByte>,
    }

    impl PersistentMemoryRegionView
    {
        pub open spec fn len(self) -> nat
        {
            self.state.len()
        }

        pub open spec fn no_outstanding_writes_in_range(self, i: int, j: int) -> bool
        {
            forall |k| i <= k < j ==> (#[trigger] self.state[k].outstanding_write).is_none()
        }

        pub open spec fn committed(self) -> Seq<u8>
        {
            self.state.map(|_addr, b: PersistentMemoryByte| b.state_at_last_flush)
        }

        pub open spec fn chunk_corresponds_ignoring_outstanding_writes(self, chunk: int, bytes: Seq<u8>) -> bool
        {
            forall |addr: int| {
                &&& 0 <= addr < self.len()
                &&& addr / const_persistence_chunk_size() == chunk
            } ==> #[trigger] bytes[addr] == self.state[addr].state_at_last_flush
        }

        pub open spec fn chunk_corresponds_after_flush(self, chunk: int, bytes: Seq<u8>) -> bool
        {
            forall |addr: int| {
                &&& 0 <= addr < self.len()
                &&& addr / const_persistence_chunk_size() == chunk
            } ==> #[trigger] bytes[addr] == self.state[addr].flush_byte()
        }

        pub open spec fn can_crash_as(self, bytes: Seq<u8>) -> bool
        {
            &&& bytes.len() == self.len()
            &&& forall |chunk| {
                  ||| self.chunk_corresponds_ignoring_outstanding_writes(chunk, bytes)
                  ||| self.chunk_corresponds_after_flush(chunk, bytes)
              }
        }
    }

    pub struct PersistentMemoryConstants {
        pub impervious_to_corruption: bool
    }

    pub trait PersistentMemoryRegion : Sized
    {
 
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
                        &&& // If the persistent memory regions are impervious
                            // to corruption, read returns the last bytes
                            // written. Otherwise, it returns a
                            // possibly-corrupted version of those bytes.
                            if self.constants().impervious_to_corruption {
                                bytes@ == true_bytes
                            }
                            else {
                                maybe_corrupted(bytes@, true_bytes, addrs)
                            }
                        }
                    _ => false,
                }
        ;
    }

    pub open spec fn extract_bytes(bytes: Seq<u8>, pos: nat, len: nat) -> Seq<u8>
    {
        bytes.subrange(pos as int, (pos + len) as int)
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
    PersistentMemoryRegionView{ state: region.state.subrange(start as int, (start + len) as int) }
}

/*pmem\wrpm_t*/
pub trait CheckPermission<State>
{
    spec fn check_permission(&self, state: State) -> bool;
}

#[allow(dead_code)]
pub struct WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>
    where
        Perm: CheckPermission<Seq<u8>>,
        PMRegion: PersistentMemoryRegion
{
    pm_region: PMRegion,
    ghost perm: Option<Perm>, // Needed to work around Rust limitation that Perm must be referenced
}

impl<Perm, PMRegion> WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>
    where
        Perm: CheckPermission<Seq<u8>>,
        PMRegion: PersistentMemoryRegion
{
 
	#[verifier::external_body]
    pub closed spec fn view(&self) -> PersistentMemoryRegionView
	{
		unimplemented!()
	}

	#[verifier::external_body]
    pub closed spec fn inv(&self) -> bool
	{
		unimplemented!()
	}

	#[verifier::external_body]
    pub closed spec fn constants(&self) -> PersistentMemoryConstants
	{
		unimplemented!()
	}

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
    /*pmem\traits_t*/
    #[verifier::external_trait_specification]
    pub trait ExPmSized : SpecPmSized {
        type ExternalTraitSpecificationFor: PmSized;

        fn size_of() -> (out: usize)
            ensures 
                out as int == Self::spec_size_of();
        fn align_of() -> (out: usize)
            ensures 
                out as int == Self::spec_align_of();
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
            out as nat == S::spec_size_of()
    {
        S::size_of()
    }

    pub fn align_of<S: PmSized>() -> (out: usize)
        ensures 
            out as nat == S::spec_align_of()
    {
        S::align_of()
    }
}

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
pub unsafe trait PmSized : SpecPmSized {
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
    fn size_of() -> usize 
    {
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


