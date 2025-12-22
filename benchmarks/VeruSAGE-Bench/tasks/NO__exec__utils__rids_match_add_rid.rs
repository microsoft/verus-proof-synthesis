use vstd::prelude::*;

fn main() {}
pub type ReqId = nat;

verus!{

// File: exec/utils.rs
pub open spec fn rids_match(
    bools: Seq<Option<ReqId>>,
    rids: Seq<ReqId>,
    bools_start: nat,
    bools_end: nat,
    rids_start: nat,
    rids_end: nat,
) -> bool
    decreases bools_end - bools_start,
    when 0 <= bools_start <= bools_end <= bools.len() && 0 <= rids_start <= rids_end <= rids.len()
{
    if bools_end == bools_start {
        rids_end == rids_start
    } else {
        if bools[bools_end - 1].is_Some() {
            &&& rids_end > rids_start
            &&& rids[rids_end - 1] == bools[bools_end - 1].get_Some_0()
            &&& rids_match(
                bools,
                rids,
                bools_start,
                (bools_end - 1) as nat,
                rids_start,
                (rids_end - 1) as nat,
            )
        } else {
            rids_match(bools, rids, bools_start, (bools_end - 1) as nat, rids_start, rids_end)
        }
    }
}

pub proof fn rids_match_add_rid(
    bools: Seq<Option<ReqId>>,
    rids: Seq<ReqId>,
    bools_start: nat,
    bools_end: nat,
    rids_start: nat,
    rids_end: nat,
    rid: ReqId,
)
    requires
        0 <= bools_start <= bools_end <= bools.len(),
        0 <= rids_start <= rids_end <= rids.len(),
        rids_match(bools, rids, bools_start, bools_end, rids_start, rids_end),
    ensures
        rids_match(
            bools.push(Option::Some(rid)),
            rids.push(rid),
            bools_start,
            bools_end,
            rids_start,
            rids_end,
        ),
{
}


}
