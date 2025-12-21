use builtin::*;
use vstd::arithmetic::div_mod::*;
use vstd::prelude::*;

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

/*log\layout_v*/

pub const MIN_LOG_AREA_SIZE: u64 = 1;

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
    #[verifier::auto_ext_equal(assert, assert_by, ensures)]
    proof fn lemma_check_fast_way_to_compute_head_mod_log_area_len(
        info: LogInfo,
        state: AbstractLogState,
        new_head: u128,
    )
        requires
            info.head <= new_head,
            new_head - info.head <= info.log_length as u128,
            info.log_area_len >= MIN_LOG_AREA_SIZE,
            info.log_length <= info.log_plus_pending_length <= info.log_area_len,
            info.head_log_area_offset == info.head as int % info.log_area_len as int,
        ensures
            ({
                let amount_of_advancement: u64 = (new_head - info.head) as u64;
                new_head as int % info.log_area_len as int == if amount_of_advancement
                    < info.log_area_len - info.head_log_area_offset {
                    amount_of_advancement + info.head_log_area_offset
                } else {
                    amount_of_advancement - (info.log_area_len - info.head_log_area_offset)
                }
            }),
    {
    }
}

} // verus!
