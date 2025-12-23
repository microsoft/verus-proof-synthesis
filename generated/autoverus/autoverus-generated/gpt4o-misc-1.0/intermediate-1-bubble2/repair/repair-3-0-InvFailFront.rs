
use vstd::prelude::*;
fn main() {}
verus! {
    #[verifier::loop_isolation(false)]
    spec fn sorted_between(a: Seq<u32>, from: int, to: int) -> bool {
        forall|i: int, j: int| from <= i < j < to ==> a[i] <= a[j]
    }

    spec fn is_reorder_of<T>(r: Seq<int>, p: Seq<T>, s: Seq<T>) -> bool {
        &&& r.len() == s.len()
        &&& forall|i: int| 0 <= i < r.len() ==> 0 <= # [trigger] r[i] < r.len()
        &&& forall|i: int, j: int| 0 <= i < j < r.len() ==> r[i] != r[j]
        &&& p =~= r.map_values(|i: int| s[i])
    }

    fn test1(nums: &mut Vec<u32>)
        ensures
            sorted_between(nums@, 0, nums@.len() as int),
            exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@),
    {
        let n = nums.len();
        if n == 0 {
            proof {
                let r = Seq::new(0, |i: int| i);
                assert(is_reorder_of(r, nums@, nums@));
            }
            return;
        }
        proof {
            let r = Seq::new(nums@.len(), |i: int| i);
            assert(is_reorder_of(r, nums@, nums@));
        }
        for i in 1..n
        invariant
            sorted_between(nums@, 0, i as int),
            exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@),
            nums.len() == n,    // <- Add invariant here for outer loop
        {
            let mut j = i;
            while j != 0
                invariant
                    0 <= j <= i < n,
                    exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@),
                    forall|k: int| 1 <= k <= i ==> sorted_between(nums@, 0, k),
                    nums.len() == n,
                    1 <= i < n,
            {
                if nums[j - 1] > nums[j] {
                    let temp = nums[j - 1];
                    nums.set(j - 1, nums[j]);
                    nums.set(j, temp);
                }
                proof {
                    assert(exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@)); // Adding assertion within loop in case of reorder
                }
                j -= 1;
            }
        }
    }
} // verus!


//                 nums.len() == n,
//   None: nums.len() == n

// Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 3
// Safe: True