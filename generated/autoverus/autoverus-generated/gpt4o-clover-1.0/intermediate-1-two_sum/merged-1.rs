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
            ((0 <= ii && ii < r.0 && ii < jj && jj < nums.len()) || (ii == r.0 && ii < jj && jj
                < r.1)) ==> nums[ii] + nums[jj] != target,
{
    let n = nums.len();
    let mut i = 0;
    let mut j = 1;
    while i < n - 1
        invariant
            0 <= i < n - 1,
            exists|ii: int, jj: int|
                (0 <= ii && ii < jj && jj < nums.len()) && nums[ii] + nums[jj] == target,
            forall|ii: int, jj: int|
                (0 <= ii && ii < i && ii < jj && jj < nums.len()) ==> nums[ii] + nums[jj] != target,
            0 <= i < n,
            exists|ii: int, jj: int|
                (i <= ii < jj && jj < nums.len()) && nums[ii] + nums[jj] == target,
            forall|ii: int, jj: int|
                (0 <= ii && ii < nums.len() && ii < jj && jj < nums.len()) ==> nums[ii] + nums[jj]
                    < 256,
            n == nums.len(),
            nums.len() > 1,
            n > 1,
    {
        j = i + 1;
        while j < n
            invariant
                0 <= i < n - 1,
                0 <= j < n,
                exists|ii: int, kk: int|
                    (0 <= ii && ii < kk && kk < nums.len()) && nums[ii] + nums[kk] == target,
                forall|jj: int, kk: int|
                    (0 <= jj && jj < i && jj < kk && kk < nums.len()) ==> nums[jj] + nums[kk]
                        != target,
                forall|jj: int, kk: int|
                    (0 <= jj && jj < nums.len() && jj < kk && kk < nums.len()) ==> nums[jj]
                        + nums[kk] < 256,
                forall|kk: int| i + 1 <= kk < j ==> nums[(i) as int] + nums[kk] != target,
                i + 1 <= j < n,
                n == nums.len(),
                nums.len() > 1,
                0 <= i < n,
                exists|ii: int, jj: int|
                    (i <= ii < jj && jj < nums.len()) && nums[ii] + nums[jj] == target,
                forall|ii: int, jj: int|
                    (0 <= ii && ii < nums.len() && ii < jj && jj < nums.len()) ==> nums[ii]
                        + nums[jj] < 256,
                i < j <= n,
                n > 1,
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


// Score: Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 2