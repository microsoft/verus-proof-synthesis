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
        0 <= i <= nums.len(),
        res@.no_duplicates(),
        seq_to_set_rec(nums@.take(i as int)).ext_equal(res@.to_set())
    {
        let mut found = false;
        let mut j = 0;

        while j < res.len()
        invariant
            0 <= j <= res.len(),
        {
            if nums[i] == res[j] {
                found = true;
                break;
            }
            j += 1;
        }
        
        if !found {
            res.push(nums[i]);
            proof {
                assert(res@.no_duplicates() && seq_to_set_rec(nums@.take(i as int + 1)).ext_equal(res@.to_set())) by {
                    assert(nums@.take(i as int + 1).drop_last() == nums@.take(i as int));
                };
            }
        }
        i += 1;
    }
    res
}
}
// Score: (1, 4)
// Safe: True