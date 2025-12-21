use vstd::prelude::*;

verus! {

fn main() {
}

/***********log\logspec_t.rs**********/

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

/***********log\logimpl_v.rs***********/

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

/***********log\layout_v.rs*************/

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

/***********log\inv_v.rs*****************/

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

pub open spec fn log_area_offset_unreachable_during_recovery(
    head_log_area_offset: int,
    log_area_len: int,
    log_length: int,
    log_area_offset: int,
) -> bool {
    log_area_offset_to_relative_log_pos(log_area_offset, head_log_area_offset, log_area_len)
        >= log_length
}

/*********pmem\pmemspec_t.rs********/

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

/************log\append_v.rs************/

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
            &&& num_bytes > max_len_without_wrapping  // wrapping is required
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
            // The first write doesn't conflict with any outstanding writes
            &&& pm_region_view.no_outstanding_writes_in_range(
                write_addr,
                write_addr + bytes_to_append_part1.len(),
            )
            // The first write is only to log area offsets unreachable during recovery
            &&& forall|log_area_offset: int|
                write_addr <= log_area_offset < write_addr + bytes_to_append_part1.len()
                    ==> log_area_offset_unreachable_during_recovery(
                    prev_info.head_log_area_offset as int,
                    prev_info.log_area_len as int,
                    prev_info.log_length as int,
                    log_area_offset,
                )
            // The second write also doesn't conflict with any outstanding writes
            &&& pm_region_view2.no_outstanding_writes_in_range(
                0int,
                bytes_to_append_part2.len() as int,
            )
            // The second write is also only to log area offsets unreachable during recovery
            &&& forall|log_area_offset: int|
                0 <= log_area_offset < bytes_to_append_part2.len()
                    ==> log_area_offset_unreachable_during_recovery(
                    prev_info.head_log_area_offset as int,
                    prev_info.log_area_len as int,
                    prev_info.log_length as int,
                    log_area_offset,
                )
            // After the writes, the log area will be consistent with an updated info and state.
            &&& info_consistent_with_log_area(pm_region_view3, new_info, new_state)
        }),
{
}

} // verus!
