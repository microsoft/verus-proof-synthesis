#[allow(unused_imports)]
use vstd::prelude::*;
fn main() {}

verus! {
spec fn seq_to_set_rec<A>(seq: Seq<A>) -> Set<A>
    decreases seq.len()
{
    if seq.len() == 0 {
        Set::empty()
    } else {
        seq_to_set_rec(seq.drop_last()).insert(seq.last())
    }
}

fn remove_duplicates(nums: Vec<i32>) -> (res: Vec<i32>)
ensures
    res@.no_duplicates(),
    nums@.to_set().ext_equal(res@.to_set())
{
    let mut res = Vec::new();
    let mut i = 0;
    while i < nums.len()
        invariant
            i <= nums.len(),
            res.len() <= nums.len(),
            res@.no_duplicates(),
            nums@.subrange(0, i as int).to_set().ext_equal(res@.to_set()),
    {
        let mut found = false;
        let mut j = 0;
        while j < res.len()
            invariant
                j <= res.len(),
                found == exists |n:int| 0 <= n < j && nums[( i ) as int] == res[n],
        {
            if nums[i] == res[j] {
                found = true;
                break;
            }
            j += 1;
        }
        if !found {
            res.push(nums[i]);
        }
        i += 1;
    }
    res
}
}

// is safe: True
// Score: Compilation Error: False, Verified: 1, Errors: 3, Verus Errors: 6