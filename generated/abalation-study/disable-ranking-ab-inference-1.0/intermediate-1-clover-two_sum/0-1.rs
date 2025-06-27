use vstd::prelude::*;

fn main() {}

verus! {

fn two_sum(nums: &Vec<u32>, target: u32) -> (r: (usize, usize))
    requires
        nums.len() > 1,
        forall|ii: int, jj: int|
            ((0 <= ii && ii < nums.len() && ii < jj && jj < nums.len())) ==> nums[ii] + nums[jj]
                < 256,
        exists|i: int, j: int| (0 <= i && i < j && j < nums.len()) && nums[i] + nums[j] == target,
    ensures
        (0 <= r.0 && r.0 < r.1 && r.1 < nums.len()) && nums[r.0 as int] + nums[r.1 as int]
            == target,
        forall|ii: int, jj: int|
            ((0 <= ii && ii < r.0 && ii < jj && jj <nums.len())||(ii == r.0 &&ii<jj &&jj<r.1))==>
               nums[ii] + nums[jj] != target,
{
    let n = nums.len();
    let mut i = 0;
    let mut j = 1;

    while i < n - 1
        invariant
            nums.len() > 1,
            nums.len() == n,
            0 <= i <= n - 1,
            forall|ii: int, jj: int|
                ((0 <= ii && ii <nums.len() && ii < jj && jj <nums.len()))==> nums[ii] + nums[jj]
                    < 256,
    {
        j = i + 1;

        while j < n
            invariant
                nums.len() > 1,
                nums.len() == n,
                0 <= i < j <= n,
                forall|ii: int, jj: int|
                    ((0 <= ii && ii <nums.len() && ii < jj && jj <nums.len()))==> nums[ii] +
                    nums[jj] < 256,
                forall|ii: int, jj: int|
                    ((0 <= ii && ii < i && ii < jj && jj < nums.len()) || (ii == i && ii < jj && jj
                        < j)) ==> nums[ii] + nums[jj] != target,
        {
            if nums[i] + nums[j] == target {
                return (i, j);
            }
            j += 1;
        }
        i += 1;
    }
    (i, j)
}

} // verus!

// is safe: True
// Score: Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 3