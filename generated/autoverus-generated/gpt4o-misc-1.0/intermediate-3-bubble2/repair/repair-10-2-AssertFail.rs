use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

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
        return;
    }
    proof {
        let r = Seq::new(nums@.len(), |i: int| i);
        assert(is_reorder_of(r, nums@, nums@));
    }
    for i in 1..n
        invariant
            0 <= i <= n,
            exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@),
            nums.len() == n,
            sorted_between(nums@, 0, i as int),
    {
        let mut j = i;
        while j != 0
            invariant
                0 <= j <= i,
                exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@),
                nums.len() == n,
                sorted_between(nums@, 0, j as int),
                sorted_between(nums@, j as int, i as int),
        {
            if nums[j - 1] > nums[j] {
                let temp = nums[j - 1];
                nums.set(j - 1, nums[j]);
                nums.set(j, temp);
            }
            j -= 1;
        }
        proof {
            if i < n {
                assert(sorted_between(nums@, 0, i as int + 1));
                assert(exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@));
            }
        }
    }
    proof {
        assert(sorted_between(nums@, 0, n as int));
    }
}

}

//                 assert(sorted_between(nums@, j as int, i + 1)); // Added by AI
//   assertion failed: sorted_between(nums@, j as int, i + 1)

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: True