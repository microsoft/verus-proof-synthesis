
use vstd::prelude::*;
fn main() {}

verus! {
    spec fn is_reorder_of<T>(r: Seq<int>, p: Seq<T>, s: Seq<T>) -> bool {
        &&& r.len() == s.len()
        &&& forall|i: int| 0 <= i < r.len() ==> 0 <= #[trigger] r[i] < r.len()
        &&& forall|i: int, j: int| 0 <= i < j < r.len() ==> r[i] != r[j]
        &&& p == r.map(|i: int| s[i])
    }

    proof fn test1_proof(nums: &Seq<u32>) {
        let r = Seq::new(nums.len(), |i: int| i);
        assert(is_reorder_of(r, nums, nums));
    }

    #[verifier::spec]
    fn sorted_between(a: &Seq<u32>, from: int, to: int) -> bool {
        forall(|i: int, j: int| from <= i < j < to ==> a[i] <= a[j])
    }

    fn test1(nums: &mut Vec<u32>)
        ensures
            sorted_between(&nums@, 0, nums@.len() as int),
            exists|r: Seq<int>| is_reorder_of(r, &nums@, &old(nums)@),
    {
        if nums.len() == 0 {
            proof {
                let original_nums = old(nums)@;
                let r = Seq::new(original_nums.len(), |i: int| i);
                assert(is_reorder_of(r, &original_nums, &original_nums));
            }
            return;
        }
 
        for i in 1..nums.len()
            invariant
                sorted_between(&nums@, 0, i as int),
                exists|r: Seq<int>| is_reorder_of(r, &nums@, &old(nums)@),
        {
            let mut j = i;
            while j != 0
                invariant
                    sorted_between(&nums@, 0, j as int),
                    exists|r: Seq<int>| is_reorder_of(r, &nums@, &old(nums)@),
            {
                if nums[j - 1] > nums[j] {
                    proof {
                        let old_r = choose|r: Seq<int>| is_reorder_of(r, &nums@, &old(nums)@);
                        let new_r = old_r.update(j-1, old_r[j as int]).update(j as int, old_r[j-1]);
                        let updated_nums = nums@.update(j-1, nums@[j as int]).update(j as int, nums@[j-1]);
                        assert(is_reorder_of(new_r, &updated_nums, &old(nums)@));
                    }
                    nums.swap(j - 1, j);
                }
                j -= 1;
            }
        }

        proof {
            let original_nums = old(nums)@;
            let r = Seq::new(nums.len(), |i: int| i);
            assert(is_reorder_of(r, &nums@, &original_nums));
        }
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpegsu4up6`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False