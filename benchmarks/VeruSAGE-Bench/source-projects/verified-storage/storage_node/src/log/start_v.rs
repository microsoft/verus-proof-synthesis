//! This file contains functions for starting to use persistent memory
//! as a log. Such starting is done either after setup or after a
//! crash.
//!
//! The code in this file is verified and untrusted (as indicated by
//! the `_v.rs` suffix), so you don't have to read it to be confident
//! of the system's correctness.

use crate::log::inv_v::*;
use crate::log::layout_v::*;
use crate::log::logimpl_t::LogErr;
use crate::log::logimpl_v::LogInfo;
use crate::log::logspec_t::AbstractLogState;
use crate::pmem::pmemspec_t::{extract_bytes, PersistentMemoryRegion, PmemError, spec_crc_bytes};
use crate::pmem::pmemutil_v::{check_cdb, check_crc};
use crate::pmem::pmcopy_t::*;
use crate::pmem::subregion_v::*;
use crate::pmem::traits_t::size_of;
use builtin::*;
use builtin_macros::*;
use vstd::arithmetic::div_mod::*;
use vstd::bytes::*;
use vstd::prelude::*;
use vstd::slice::*;

verus! {

    // This exported function reads the corruption-detecting boolean
    // and returns it.
    //
    // `pm_region` -- the persistent-memory region to read from
    //
    // The result is a `Result<bool, LogErr>` with the following meanings:
    //
    // `Err(LogErr::CRCMismatch)` -- The CDB couldn't be read due
    // to a CRC error.
    //
    // `Ok(b)` -- The CDB could be read and represents the boolean `b`.
    pub fn read_cdb<PMRegion: PersistentMemoryRegion>(pm_region: &PMRegion) -> (result: Result<bool, LogErr>)
        requires
            pm_region.inv(),
            recover_cdb(pm_region@.committed()).is_Some(),
            pm_region@.no_outstanding_writes(),
            metadata_types_set(pm_region@.committed()),
        ensures
            match result {
                Ok(b) => Some(b) == recover_cdb(pm_region@.committed()),
                // To make sure this code doesn't spuriously generate CRC-mismatch errors,
                // it's obligated to prove that it won't generate such an error when
                // the persistent memory is impervious to corruption.
                Err(LogErr::CRCMismatch) => !pm_region.constants().impervious_to_corruption,
                Err(e) => e == LogErr::PmemErr{ err: PmemError::AccessOutOfRange },
            }
    {
        let ghost mem = pm_region@.committed();
        let ghost log_cdb_addrs = Seq::new(u64::spec_size_of() as nat, |i: int| ABSOLUTE_POS_OF_LOG_CDB + i);

        let ghost true_cdb_bytes = mem.subrange(ABSOLUTE_POS_OF_LOG_CDB as int,
                                                ABSOLUTE_POS_OF_LOG_CDB + u64::spec_size_of());
        // check_cdb does not require that the true bytes be contiguous, so we need to make Z3 confirm that the 
        // contiguous region we are using as the true value matches the address sequence we pass in.
        assert(true_cdb_bytes == Seq::new(u64::spec_size_of() as nat, |i: int| mem[log_cdb_addrs[i]]));

        let log_cdb = match pm_region.read_aligned::<u64>(ABSOLUTE_POS_OF_LOG_CDB) {
            Ok(log_cdb) => log_cdb,
            Err(e) => return Err(LogErr::PmemErr{ err: e }),
        };
        
        let result = check_cdb(log_cdb, Ghost(mem),
                               Ghost(pm_region.constants().impervious_to_corruption),
                               Ghost(log_cdb_addrs));
        match result {
            Some(b) => Ok(b),
            None => Err(LogErr::CRCMismatch)
        }
    }

    // This function reads the log information for a single log from
    // persistent memory.
    //
    // `pm_region` -- the persistent memory region to read from
    //
    // `log_id` -- the GUID of the log
    //
    // `cdb` -- the corruption-detection boolean
    //
    // The result is a `Result<LogInfo, LogErr>` with the following meanings:
    //
    // `Ok(log_info)` -- The information `log_info` has been
    // successfully read.
    //
    // `Err(LogErr::CRCMismatch)` -- The region couldn't be read due
    // to a CRC error when reading data.
    //
    // `Err(LogErr::StartFailedDueToProgramVersionNumberUnsupported)`
    // -- The program version number stored in persistent memory is
    // one that this code doesn't know how to recover from. It was
    // presumably created by a later version of this code.
    //
    // `Err(LogErr::StartFailedDueToLogIDMismatch)` -- The
    // log ID stored in persistent memory doesn't match the one
    // passed to the `start` routine. So the caller of `start` gave
    // the wrong persistent memory region or the wrong ID.
    //
    // `Err(LogErr::StartFailedDueToRegionSizeMismatch)` -- The
    // region size stored in persistent memory doesn't match the size
    // of the region passed to the `start` routine. So the caller of
    // `start` is likely using a persistent memory region that starts
    // in the right place but ends in the wrong place.
    //
    // `Err(LogErr::StartFailedDueToInvalidMemoryContents)` --
    // The region's contents aren't valid, i.e., they're not
    // recoverable to a valid log. The user must have requested to
    // start using the wrong region of persistent memory.
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
                    Err(LogErr::CRCMismatch) =>
                        state.is_Some() ==> !pm_region.constants().impervious_to_corruption,
                    Err(LogErr::StartFailedDueToInvalidMemoryContents) => {
                        ||| pm_region@.len() < ABSOLUTE_POS_OF_LOG_AREA + MIN_LOG_AREA_SIZE
                        ||| state is None
                    },
                    Err(LogErr::StartFailedDueToProgramVersionNumberUnsupported{ version_number, max_supported}) => {
                        &&& state is None 
                        &&& version_number != max_supported
                    },
                    Err(LogErr::StartFailedDueToLogIDMismatch { log_id_expected, log_id_read }) => {
                        &&& state is None 
                        &&& log_id_expected != log_id_read
                    }
                    Err(LogErr::StartFailedDueToRegionSizeMismatch { region_size_expected, region_size_read }) => {
                        &&& state is None 
                        &&& region_size_expected != region_size_read
                    }
                    _ => false,
                }
            })
    {
        let ghost mem = pm_region@.committed();
        let ghost state = recover_given_cdb(pm_region@.committed(), log_id, cdb);
        reveal(spec_padding_needed);

        // Check that the region is at least the minimum required size. If
        // not, indicate invalid memory contents.

        let region_size = pm_region.get_region_size();
        if region_size < ABSOLUTE_POS_OF_LOG_AREA + MIN_LOG_AREA_SIZE {
            assert(state.is_None()); // This can't happen if the persistent memory is recoverable
            return Err(LogErr::StartFailedDueToInvalidMemoryContents)
        }
        
        // Obtain the true global metadata and CRC. The precondition ensures that a true value exists for each.
        let ghost true_global_metadata = GlobalMetadata::spec_from_bytes(extract_bytes(mem, ABSOLUTE_POS_OF_GLOBAL_METADATA as nat, GlobalMetadata::spec_size_of()));
        let ghost true_crc = u64::spec_from_bytes(extract_bytes(mem, ABSOLUTE_POS_OF_GLOBAL_CRC as nat, u64::spec_size_of()));

        // Read the global metadata struct and CRC from PM. We still have to prove that they are not corrupted before we can use the metadata.
        let global_metadata = match pm_region.read_aligned::<GlobalMetadata>(ABSOLUTE_POS_OF_GLOBAL_METADATA) {
            Ok(global_metadata) => global_metadata,
            Err(e) => {
                assert(false);
                return Err(LogErr::PmemErr { err: e });
            }
        };
        let global_crc = match pm_region.read_aligned::<u64>(ABSOLUTE_POS_OF_GLOBAL_CRC) {
            Ok(global_crc) => global_crc,
            Err(e) => {
                assert(false);
                return Err(LogErr::PmemErr { err: e });
            }
        };

        // Check whether the bytes we read are corrupted; if they aren't, we can safely cast the global metadata bytes to a GlobalMetadata
        // and access its fields.
        let ghost global_metadata_addrs = Seq::new(GlobalMetadata::spec_size_of() as nat, |i: int| ABSOLUTE_POS_OF_GLOBAL_METADATA + i);
        let ghost crc_addrs = Seq::new(u64::spec_size_of() as nat, |i: int| ABSOLUTE_POS_OF_GLOBAL_CRC + i);
        let ghost true_bytes = Seq::new(GlobalMetadata::spec_size_of()as nat, |i: int| mem[global_metadata_addrs[i] as int]);
        let ghost true_crc_bytes = Seq::new(u64::spec_size_of() as nat, |i: int| mem[crc_addrs[i] as int]);
        assert(true_global_metadata.spec_to_bytes() == true_bytes && true_crc.spec_to_bytes() == true_crc_bytes);

        if !check_crc(global_metadata.as_slice(), global_crc.as_slice(),
                      Ghost(mem), Ghost(pm_region.constants().impervious_to_corruption),
                      Ghost(global_metadata_addrs), 
                      Ghost(crc_addrs)) {
            return Err(LogErr::CRCMismatch);
        }

        let global_metadata = global_metadata.extract_init_val(
            Ghost(true_global_metadata), 
            Ghost(true_bytes), 
            Ghost(pm_region.constants().impervious_to_corruption)
        );

        // Check the global metadata for validity. If it isn't valid,
        // e.g., due to the program GUID not matching, then return an
        // error. Such invalidity can't happen if the persistent
        // memory is recoverable.

        if global_metadata.program_guid != LOG_PROGRAM_GUID {
            assert(state.is_None()); // This can't happen if the persistent memory is recoverable
            return Err(LogErr::StartFailedDueToInvalidMemoryContents)
        }

        if global_metadata.version_number != LOG_PROGRAM_VERSION_NUMBER {
            assert(state.is_None()); // This can't happen if the persistent memory is recoverable
            return Err(LogErr::StartFailedDueToProgramVersionNumberUnsupported{
                version_number: global_metadata.version_number,
                max_supported: LOG_PROGRAM_VERSION_NUMBER,
            })
        }

        if global_metadata.length_of_region_metadata != size_of::<RegionMetadata>() as u64 {
            assert(state.is_None()); // This can't happen if the persistent memory is recoverable
            return Err(LogErr::StartFailedDueToInvalidMemoryContents)
        }

        // Read the region metadata and its CRC, and check that the
        // CRC matches.
        let ghost metadata_addrs = Seq::new(RegionMetadata::spec_size_of() as nat, |i: int| ABSOLUTE_POS_OF_REGION_METADATA + i);
        let ghost crc_addrs = Seq::new(u64::spec_size_of() as nat, |i: int| ABSOLUTE_POS_OF_REGION_CRC + i);

        let ghost true_region_metadata = RegionMetadata::spec_from_bytes(extract_bytes(mem, ABSOLUTE_POS_OF_REGION_METADATA as nat, RegionMetadata::spec_size_of()));
        let ghost true_crc = u64::spec_from_bytes(extract_bytes(mem, ABSOLUTE_POS_OF_REGION_CRC as nat, u64::spec_size_of()));

        let region_metadata = match pm_region.read_aligned::<RegionMetadata>(ABSOLUTE_POS_OF_REGION_METADATA) {
            Ok(region_metadata) => region_metadata,
            Err(e) => {
                assert(false);
                return Err(LogErr::PmemErr { err: e });
            }
        };
        let region_crc = match pm_region.read_aligned::<u64>(ABSOLUTE_POS_OF_REGION_CRC) {
            Ok(region_crc) => region_crc,
            Err(e) => {
                assert(false);
                return Err(LogErr::PmemErr { err: e });
            }
        };

        let ghost true_bytes = Seq::new(metadata_addrs.len(), |i: int| mem[metadata_addrs[i] as int]);
        let ghost true_crc_bytes = Seq::new(crc_addrs.len(), |i: int| mem[crc_addrs[i] as int]);
        assert(true_region_metadata.spec_to_bytes() == true_bytes && true_crc.spec_to_bytes() == true_crc_bytes);

        if !check_crc(region_metadata.as_slice(), region_crc.as_slice(),
                      Ghost(mem), Ghost(pm_region.constants().impervious_to_corruption),
                      Ghost(metadata_addrs),
                      Ghost(crc_addrs)) {
            return Err(LogErr::CRCMismatch);
        }

        assert(true_region_metadata.spec_to_bytes() == true_bytes);
        let region_metadata = region_metadata.extract_init_val(
            Ghost(true_region_metadata),
            Ghost(true_bytes),
            Ghost(pm_region.constants().impervious_to_corruption)
        );

        // Check the region metadata for validity. If it isn't valid,
        // e.g., due to the encoded region size not matching the
        // actual region size, then return an error. Such invalidity
        // can't happen if the persistent memory is recoverable.

        if region_metadata.region_size != region_size {
            assert(state.is_None()); // This can't happen if the persistent memory is recoverable
            return Err(LogErr::StartFailedDueToRegionSizeMismatch{
                region_size_expected: region_size,
                region_size_read: region_metadata.region_size,
            })
        }

        if region_metadata.log_id != log_id {
            assert(state.is_None()); // This can't happen if the persistent memory is recoverable
            return Err(LogErr::StartFailedDueToLogIDMismatch{
                log_id_expected: log_id,
                log_id_read: region_metadata.log_id,
            })
        }

        if region_metadata.log_area_len > region_size {
            assert(state.is_None()); // This can't happen if the persistent memory is recoverable
            return Err(LogErr::StartFailedDueToInvalidMemoryContents)
        }
        if region_size - region_metadata.log_area_len < ABSOLUTE_POS_OF_LOG_AREA {
            assert(state.is_None()); // This can't happen if the persistent memory is recoverable
            return Err(LogErr::StartFailedDueToInvalidMemoryContents)
        }
        if region_metadata.log_area_len < MIN_LOG_AREA_SIZE {
            assert(state.is_None()); // This can't happen if the persistent memory is recoverable
            return Err(LogErr::StartFailedDueToInvalidMemoryContents)
        }

        // Read the log metadata and its CRC, and check that the
        // CRC matches. The position where to find the log
        // metadata depend on the CDB.

        let log_metadata_pos = if cdb { ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_TRUE }
                                    else { ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE };
        let log_crc_pos = if cdb { ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_TRUE }
                                    else { ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_FALSE };
        assert(log_metadata_pos == get_log_metadata_pos(cdb));
        let subregion = PersistentMemorySubregion::new(pm_region, log_metadata_pos,
                                                       Ghost(LogMetadata::spec_size_of() + u64::spec_size_of()));
        let ghost true_log_metadata = LogMetadata::spec_from_bytes(extract_bytes(mem, log_metadata_pos as nat, LogMetadata::spec_size_of()));
        let ghost true_crc = u64::spec_from_bytes(extract_bytes(mem, log_crc_pos as nat, u64::spec_size_of()));
        let ghost log_metadata_addrs = Seq::new(LogMetadata::spec_size_of() as nat, |i: int| log_metadata_pos + i);
        let ghost crc_addrs = Seq::new(u64::spec_size_of() as nat, |i: int| log_crc_pos + i);
        let ghost true_bytes = Seq::new(log_metadata_addrs.len(), |i: int| mem[log_metadata_addrs[i] as int]);
        let ghost true_crc_bytes = Seq::new(crc_addrs.len(), |i: int| mem[crc_addrs[i] as int]);

        assert(pm_region@.committed().subrange(log_metadata_pos as int, log_metadata_pos + LogMetadata::spec_size_of()) == true_bytes);
        let log_metadata = match pm_region.read_aligned::<LogMetadata>(log_metadata_pos) {
            Ok(log_metadata) => log_metadata,
            Err(e) => {
                assert(false);
                return Err(LogErr::PmemErr { err: e });
            }
        };
        let log_crc = match pm_region.read_aligned::<u64>(log_crc_pos) {
            Ok(log_crc) => log_crc,
            Err(e) => {
                assert(false);
                return Err(LogErr::PmemErr { err: e });
            }
        };

        assert(true_log_metadata.spec_to_bytes() == true_bytes && true_crc.spec_to_bytes() == true_crc_bytes);

        if !check_crc(log_metadata.as_slice(), log_crc.as_slice(), Ghost(mem),
                                   Ghost(pm_region.constants().impervious_to_corruption),
                                    Ghost(log_metadata_addrs), Ghost(crc_addrs)) {
            return Err(LogErr::CRCMismatch);
        }

        let log_metadata = log_metadata.extract_init_val(
            Ghost(true_log_metadata), 
            Ghost(true_bytes),
            Ghost(pm_region.constants().impervious_to_corruption)
        );

        // Check the log metadata for validity. If it isn't valid,
        // e.g., due to the log length being greater than the log area
        // length, then return an error. Such invalidity can't happen
        // if the persistent memory is recoverable.

        let head = log_metadata.head;
        let log_length = log_metadata.log_length;
        if log_length > region_metadata.log_area_len {
            assert(state.is_None()); // This can't happen if the persistent memory is recoverable
            return Err(LogErr::StartFailedDueToInvalidMemoryContents)
        }
        if log_length as u128 > u128::MAX - head {
            assert(state.is_None()); // This can't happen if the persistent memory is recoverable
            return Err(LogErr::StartFailedDueToInvalidMemoryContents)
        }

        // Compute the offset into the log area where the head of the
        // log is. This is the u128 `head` mod the u64
        // `log_area_len`. To prove that this will fit in a `u64`, we
        // need to invoke a math lemma saying that the result of a
        // modulo operation is always less than the divisor.

        proof { lemma_mod_bound(head as int, region_metadata.log_area_len as int); }
        let head_log_area_offset: u64 = (head % region_metadata.log_area_len as u128) as u64;

        // Return the log info. This necessitates computing the
        // pending tail position relative to the head, but this is
        // easy: It's the same as the log length. This is because,
        // upon recovery, there are no pending appends beyond the tail
        // of the log.

        Ok(LogInfo{
            log_area_len: region_metadata.log_area_len,
            head,
            head_log_area_offset,
            log_length,
            log_plus_pending_length: log_length
        })
    }
}
