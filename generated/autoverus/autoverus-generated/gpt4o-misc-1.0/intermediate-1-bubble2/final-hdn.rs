use vstd::prelude::*;
fn main() {}

verus! {

spec fn sorted_between(a: Seq<u32>, from: int, to: int) -> bool {
    forall|i: int, j: int| from <= i < j < to ==> a[i] <= a[j]
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
            let r = Seq::new(0, |i: int| i);
            assert(is_reorder_of(r, nums@, nums@));
        }
        return;
    }
    let ghost mut r = Seq::new(nums@.len(), |i: int| i); // Initialized reorder sequence
    proof {
        assert(is_reorder_of(r, nums@, nums@)); // Validating reorder sequence
    }
    for i in 1..n
    invariant
        nums.len() == n, // Keeping length invariant
    {
        let mut j = i;
        proof {
        }
        while j != 0
        invariant
            0 <= j <= i < n,
            n == nums.len(),
        {
            if nums[j - 1] > nums[j] {
                proof {
                    let r1 = choose |r: Seq<int>| is_reorder_of(r, nums@, old(nums)@);
                    r = r.update(j as int - 1, r[j as int]).update(j as int, r[j as int - 1]); // Update reorder sequence
                }
                let temp = nums[j - 1];
                nums.set(j - 1, nums[j]);
                nums.set(j, temp);
            }
            proof {
            }
            j -= 1;
        }
    }
}
}

// Score: Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 2