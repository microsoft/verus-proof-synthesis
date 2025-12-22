use vstd::prelude::*;
use vstd::arithmetic::div_mod::*;


verus! {

    pub fn main()
    {
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

    impl UntrustedLogImpl{

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
                    new_head as int % info.log_area_len as int ==
                        if amount_of_advancement < info.log_area_len - info.head_log_area_offset {
                            amount_of_advancement + info.head_log_area_offset
                        }
                        else {
                            amount_of_advancement - (info.log_area_len - info.head_log_area_offset)
                        }
                }),
        {
            let amount_of_advancement: u64 = (new_head - info.head) as u64;
            let new_head_log_area_offset =
                if amount_of_advancement < info.log_area_len - info.head_log_area_offset {
                    amount_of_advancement + info.head_log_area_offset
                }
                else {
                    amount_of_advancement - (info.log_area_len - info.head_log_area_offset)
                };

            let n = info.log_area_len as int;
            let advancement = amount_of_advancement as int;
            let head = info.head as int;
            let head_mod_n = info.head_log_area_offset as int;
            let supposed_new_head_mod_n = new_head_log_area_offset as int;

            // First, observe that `advancement` plus `head` is
            // congruent modulo n to `advancement` plus `head` % n.

            assert((advancement + head) % n == (advancement + head_mod_n) % n) by {
                assert(head == n * (head / n) + head % n) by {
                    lemma_fundamental_div_mod(head, n);
                }
                assert((n * (head / n) + (advancement + head_mod_n)) % n == (advancement + head_mod_n) % n) by {
                    lemma_mod_multiples_vanish(head / n, advancement + head_mod_n, n);
                }
            }

            // Next, observe that `advancement` + `head` % n is
            // congruent modulo n to itself minus n. This is
            // relevant because there are two cases for computing
            // `new_head_mod_log_area_offset`. In one case, it's
            // computed as `advancement` + `head` % n. In the
            // other case, it's that quantity minus n.

            assert((advancement + head % n) % n == (advancement + head_mod_n - n) % n) by {
                lemma_mod_sub_multiples_vanish(advancement + head_mod_n, n);
            }

            // So we know that in either case, `new_head` % n ==
            // `new_head_mod_log_area_offset` % n.

            assert(new_head as int % n == supposed_new_head_mod_n % n);

            // But what we want to prove is that `new_head` % n ==
            // `new_head_mod_log_area_offset`. So we need to show
            // that `new_head_mod_log_area_offset` % n ==
            // `new_head_mod_log_area_offset`.  We can deduce this
            // from the fact that 0 <= `new_head_mod_log_area_offset`
            // < n.

            assert(supposed_new_head_mod_n % n == supposed_new_head_mod_n) by {
                lemma_small_mod(supposed_new_head_mod_n as nat, n as nat);
            }
        }

    }

    /*log\logspec_t*/
    pub struct AbstractLogState {
        pub head: int,
        pub log: Seq<u8>,
        pub pending: Seq<u8>,
        pub capacity: int,
    }

}
