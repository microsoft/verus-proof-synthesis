
use vstd::prelude::*;
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
            proof {
                assert(exists|r: Seq<int>| is_reorder_of(r, nums@, nums@));
            }
            return;
        }

        for i in 1..n
            invariant
                n == nums.len(),
                sorted_between(nums@, 0, i as int),
                exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@),
        {
            let mut j = i as int; // Moving it to int for better usage later.

            while j > 0
                invariant
                    0 <= j, // Invariant update
                    j <= i as int,
                    n == nums.len(),
                    forall|x: int, y: int| 0 <= x && x <= y && y <= i as int ==> x != j && y != j ==> nums[x] <= nums[y],
                    sorted_between(nums@, j as int, i + 1),
                    exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@),
            {
                if nums[(j - 1) as usize] > nums[j as usize] {
                    proof {
                        let r1 = choose|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@);
                        let r2 = r1.update((j - 1) as int, r1[j as int]).update(j as int, r1[(j - 1) as int]);
                        assert(is_reorder_of(r2,
                            nums@
                                .update((j - 1) as usize, nums[j as usize])
                                .update(j as usize, nums[(j - 1) as usize]),
                            old(nums)@
                        ));
                    }

                    let temp = nums[(j - 1) as usize];
                    nums.set((j - 1) as usize, nums[j as usize]);
                    nums.set(j as usize, temp);
                }

                j -= 1;
                proof {
                    assert(exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@));
                }
            }
        }
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpc369tzat`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 16
// Safe: False