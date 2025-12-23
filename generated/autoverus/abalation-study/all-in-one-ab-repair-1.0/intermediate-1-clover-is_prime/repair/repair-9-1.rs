
use vstd::prelude::*;
fn main() {}

verus! {
    spec fn sorted_between(a: Seq<u32>, from: int, to: int) -> bool {
        forall |i: int, j:int|  from <= i < j < to ==> a[i] <= a[j]
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
            } // Added by AI
            return;
        }
        for i in 1..n
            invariant
                n == nums.len(),
                sorted_between(nums@, 0, i as int),
                exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@),
        {
            let mut j = i;
            while j != 0
                invariant
                    0 <= j <= i < n == nums.len(),
                    forall|x: int, y: int| 0 <= x <= y <= i ==> x != j && y != j ==> nums[x] <= nums[y],
                    sorted_between(nums@, j as int, i + 1),
                    exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@),
            {
                if nums[j - 1] > nums[j] {
                    proof {
                        let r1 = choose|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@);
                        let r2 = r1.update(j-1, r1[j as int]).update(j as int, r1[j-1]);
                        assert(is_reorder_of(r2, nums@.update(j-1, nums@[j as int]).update(j as int, nums@[j-1]), old(nums)@));
                    }
                    let temp = nums[j - 1];
                    nums.set(j - 1, nums[j]);
                    nums.set(j, temp);
                }
                j -= 1;
                proof {
                    assert(exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@));
                }
            }
        }
    }
    
    // Adding the test_prime function with the earlier syntax
    spec fn divides(factor: nat, candidate: nat) -> bool {
        candidate % factor == 0
    }

    spec fn is_prime(candidate: nat) -> bool {
        &&& 1 < candidate
        &&& forall|factor: nat| 1 < factor && factor < candidate ==> !divides(factor, candidate)
    }

    fn test_prime(candidate: u64) -> bool
        requires
            1 < candidate,
        ensures
            result == is_prime(candidate as nat),
    {
        let mut factor: u64 = 2;

        while factor < candidate
            invariant
                1 < candidate,
                2 <= factor <= candidate,
                forall|f: nat| 2 <= f < factor ==> !divides(f, candidate as nat),
        {
            if candidate % factor == 0 {
                return false;
            }
            factor = factor + 1;
        }

        true
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpycjlzjur`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False