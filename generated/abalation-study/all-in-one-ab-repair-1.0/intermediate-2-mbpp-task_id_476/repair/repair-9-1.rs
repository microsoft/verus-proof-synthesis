
#![verifier::loop_isolation(false)]

use vstd::math::*;
use vstd::prelude::*;
use vstd::seq::Seq;

fn main() {}

verus! {
    spec fn sorted_between(a: Seq<u32>, from: int, to: int) -> bool {
        forall |i: int, j: int| from <= i < j < to ==> a[i] <= a[j]
    }

    spec fn is_reorder_of<T>(r: Seq<int>, p: Seq<T>, s: Seq<T>) -> bool {
        &&& r.len() == s.len()
        &&& forall|i: int| 0 <= i < r.len() ==> 0 <= #[trigger] r[i] < r.len()
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
            return;  // early return for empty vec, no changes needed to the proof as sorted and reorder trivially hold.
        }

        let old_nums = nums.clone();
        
        for i in 1..n
            invariant
                n == nums.len(),
                sorted_between(nums@, 0, i as int),
                exists|r: Seq<int>| is_reorder_of(r, nums@.take(i as int), old_nums@),
        {
            let mut j = i;
            while j != 0
                invariant
                    0 <= j <= i,
                    i < n,
                    n == nums.len(),
                    sorted_between(nums@, j as int, i + 1),
                    forall|x: int, y: int| 0 <= x <= y < i ==> x != j && y != j ==> nums[x] <= nums[y],
                    exists|r: Seq<int>| is_reorder_of(r, nums@.take(i as int), old_nums@),
            {
                if nums[j - 1] > nums[j] {
                    nums.swap(j - 1, j);
                }
                j -= 1;

                proof {
                    assert(exists|r: Seq<int>| is_reorder_of(r, nums@.take(i as int), old_nums@));
                }
            }
            proof {
                assert(sorted_between(nums@, 0, i as int));
                assert(exists|r: Seq<int>| is_reorder_of(r, nums@.take(i as int), old_nums@));
            }
        }

        proof {
            assert(sorted_between(nums@, 0, nums@.len() as int));
            assert(exists|r: Seq<int>| is_reorder_of(r, nums@, old_nums@));
        }
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpar6muukt`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False