use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::external_body]
pub proof fn lemma_tentatively_append(
    pm_region_view: PersistentMemoryRegionView,
    bytes_to_append: Seq<u8>,
    prev_info: LogInfo,
    prev_state: AbstractLogState,
)
    requires
        pm_region_view.len() == prev_info.log_area_len,
        info_consistent_with_log_area(pm_region_view, prev_info, prev_state),
        ({
            let log_area_len = prev_info.log_area_len;
            let num_bytes = bytes_to_append.len();
            let max_len_without_wrapping = log_area_len - relative_log_pos_to_log_area_offset(
                prev_info.log_plus_pending_length as int,
                prev_info.head_log_area_offset as int,
                log_area_len as int,
            );
            &&& 0 < num_bytes <= max_len_without_wrapping
            &&& prev_info.log_plus_pending_length + num_bytes <= log_area_len
            &&& prev_info.head + prev_info.log_plus_pending_length + num_bytes <= u128::MAX
        }),
    ensures
        ({
            let log_area_len = prev_info.log_area_len;
            let num_bytes = bytes_to_append.len();
            let new_info = prev_info.tentatively_append(num_bytes as u64);
            let new_state = prev_state.tentatively_append(bytes_to_append);
            let write_addr = relative_log_pos_to_log_area_offset(
                prev_info.log_plus_pending_length as int,
                prev_info.head_log_area_offset as int,
                log_area_len as int,
            );
            let pm_region_view2 = pm_region_view.write(write_addr, bytes_to_append);
            &&& pm_region_view.no_outstanding_writes_in_range(write_addr, write_addr + num_bytes)
            &&& forall|log_area_offset: int|
                write_addr <= log_area_offset < write_addr + num_bytes
                    ==> log_area_offset_unreachable_during_recovery(
                    prev_info.head_log_area_offset as int,
                    prev_info.log_area_len as int,
                    prev_info.log_length as int,
                    log_area_offset,
                )
            &&& info_consistent_with_log_area(pm_region_view2, new_info, new_state)
        }),
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn lemma_tentatively_append_wrapping(
    pm_region_view: PersistentMemoryRegionView,
    bytes_to_append: Seq<u8>,
    prev_info: LogInfo,
    prev_state: AbstractLogState,
)
    requires
        pm_region_view.len() == prev_info.log_area_len,
        info_consistent_with_log_area(pm_region_view, prev_info, prev_state),
        ({
            let log_area_len = prev_info.log_area_len;
            let num_bytes = bytes_to_append.len();
            let max_len_without_wrapping = log_area_len - relative_log_pos_to_log_area_offset(
                prev_info.log_plus_pending_length as int,
                prev_info.head_log_area_offset as int,
                log_area_len as int,
            );
            &&& num_bytes > max_len_without_wrapping
            &&& prev_info.head + prev_info.log_plus_pending_length + num_bytes <= u128::MAX
            &&& num_bytes <= log_area_len - prev_info.log_plus_pending_length
        }),
    ensures
        ({
            let log_area_len = prev_info.log_area_len;
            let max_len_without_wrapping = log_area_len - relative_log_pos_to_log_area_offset(
                prev_info.log_plus_pending_length as int,
                prev_info.head_log_area_offset as int,
                log_area_len as int,
            );
            let new_info = prev_info.tentatively_append(bytes_to_append.len() as u64);
            let new_state = prev_state.tentatively_append(bytes_to_append);
            let bytes_to_append_part1 = bytes_to_append.subrange(
                0,
                max_len_without_wrapping as int,
            );
            let bytes_to_append_part2 = bytes_to_append.subrange(
                max_len_without_wrapping as int,
                bytes_to_append.len() as int,
            );
            let write_addr = relative_log_pos_to_log_area_offset(
                prev_info.log_plus_pending_length as int,
                prev_info.head_log_area_offset as int,
                log_area_len as int,
            );
            let pm_region_view2 = pm_region_view.write(write_addr, bytes_to_append_part1);
            let pm_region_view3 = pm_region_view2.write(0int, bytes_to_append_part2);
            &&& pm_region_view.no_outstanding_writes_in_range(
                write_addr,
                write_addr + bytes_to_append_part1.len(),
            )
            &&& forall|log_area_offset: int|
                write_addr <= log_area_offset < write_addr + bytes_to_append_part1.len()
                    ==> log_area_offset_unreachable_during_recovery(
                    prev_info.head_log_area_offset as int,
                    prev_info.log_area_len as int,
                    prev_info.log_length as int,
                    log_area_offset,
                )
            &&& pm_region_view2.no_outstanding_writes_in_range(
                0int,
                bytes_to_append_part2.len() as int,
            )
            &&& forall|log_area_offset: int|
                0 <= log_area_offset < bytes_to_append_part2.len()
                    ==> log_area_offset_unreachable_during_recovery(
                    prev_info.head_log_area_offset as int,
                    prev_info.log_area_len as int,
                    prev_info.log_length as int,
                    log_area_offset,
                )
            &&& info_consistent_with_log_area(pm_region_view3, new_info, new_state)
        }),
{
    unimplemented!()
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

pub open spec fn log_area_offset_unreachable_during_recovery(
    head_log_area_offset: int,
    log_area_len: int,
    log_length: int,
    log_area_offset: int,
) -> bool {
    log_area_offset_to_relative_log_pos(log_area_offset, head_log_area_offset, log_area_len)
        >= log_length
}

pub const ABSOLUTE_POS_OF_LOG_AREA: u64 = 256;

pub const MIN_LOG_AREA_SIZE: u64 = 1;

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

#[allow(dead_code)]
pub struct TrustedPermission {
    ghost is_state_allowable: spec_fn(Seq<u8>) -> bool,
}

impl CheckPermission<Seq<u8>> for TrustedPermission {
    closed spec fn check_permission(&self, state: Seq<u8>) -> bool {
        (self.is_state_allowable)(state)
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
    pub closed spec fn view(&self) -> AbstractLogState {
        self.state@
    }

    #[verifier::auto_ext_equal(assert, assert_by, ensures)]
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
        let info = &self.info;
        let old_pending_tail: u128 = info.head + info.log_plus_pending_length as u128;
        let num_bytes: u64 = bytes_to_append.len() as u64;
        if num_bytes == 0 {
            let ret = Ok(old_pending_tail);
            return ret;
        }
        if info.log_plus_pending_length >= info.log_area_len - info.head_log_area_offset {
            let write_addr: u64 = info.log_plus_pending_length - (info.log_area_len
                - info.head_log_area_offset);
            let tracked write_relative_tracked0: &TrustedPermission = proof_from_false(); // TODO - replace with correct value 
            subregion.write_relative(wrpm_region, write_addr, bytes_to_append, Tracked(write_relative_tracked0));
        } else {
            let write_addr: u64 = info.log_plus_pending_length + info.head_log_area_offset;
            let max_len_without_wrapping: u64 = info.log_area_len - info.head_log_area_offset
                - info.log_plus_pending_length;
            if num_bytes <= max_len_without_wrapping {
                let tracked write_relative_tracked0: &TrustedPermission = proof_from_false(); // TODO - replace with correct value 
                subregion.write_relative(wrpm_region, write_addr, bytes_to_append, Tracked(write_relative_tracked0));
            } else {
                let tracked write_relative_tracked0: &TrustedPermission = proof_from_false(); // TODO - replace with correct value 
                subregion.write_relative(
                    wrpm_region,
                    write_addr,
                    slice_subrange(bytes_to_append, 0, max_len_without_wrapping as usize),
                    Tracked(write_relative_tracked0),
                );
                let tracked write_relative_tracked1: &TrustedPermission = proof_from_false(); // TODO - replace with correct value 
                subregion.write_relative(
                    wrpm_region,
                    0u64,
                    slice_subrange(
                        bytes_to_append,
                        max_len_without_wrapping as usize,
                        bytes_to_append.len(),
                    ),
                    Tracked(write_relative_tracked1),
                );
            }
        }
        let ret = Ok(old_pending_tail);
        ret
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
}

pub enum PmemError {
    InvalidFileName,
    CannotOpenPmFile,
    NotPm,
    PmdkError,
    AccessOutOfRange,
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
}

pub struct PersistentMemoryConstants {
    pub impervious_to_corruption: bool,
}

pub trait PersistentMemoryRegion: Sized {

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
    pub closed spec fn start(self) -> nat {
        unimplemented!()
    }

    #[verifier::external_body]
    pub closed spec fn len(self) -> nat {
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
    pub exec fn write_relative<Perm, PMRegion>(
        self: &Self,
        wrpm: &mut WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        relative_addr: u64,
        bytes: &[u8],
        Tracked(perm): Tracked<&Perm>,
    ) where Perm: CheckPermission<Seq<u8>>, PMRegion: PersistentMemoryRegion
        requires
            self.inv(old(wrpm), perm),
            relative_addr + bytes@.len() <= self.view(old(wrpm)).len(),
            self.view(old(wrpm)).no_outstanding_writes_in_range(
                relative_addr as int,
                relative_addr + bytes.len(),
            ),
            forall|i: int|
                relative_addr <= i < relative_addr + bytes@.len()
                    ==> self.is_writable_relative_addr(i),
        ensures
            self.inv(wrpm, perm),
            self.view(wrpm) == self.view(old(wrpm)).write(relative_addr as int, bytes@),
    {
        unimplemented!()
    }
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

pub fn main() {
}

} // verus!
