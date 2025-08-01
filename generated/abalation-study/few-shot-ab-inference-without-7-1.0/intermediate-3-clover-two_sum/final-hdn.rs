
use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

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
            0 <= i < n,
            0 <= i < n - 1,
            exists|ii: int, jj: int|
                (0 <= ii && ii < jj && jj < n) && nums[ii] + nums[jj] == target,
            exists|x: int, y: int| 0 <= x && x < y && y < n && nums[x] + nums[y] == target,
            forall|ii: int, jj: int|
                (0 <= ii && ii < i && ii < jj && jj < n) ==> nums[ii] + nums[jj] != target,
            forall|k: int, l: int|
                (0 <= k && k < i && l == k + 1 && l < n) ==> nums[k] + nums[l] != target,
            nums.len() > 1,
            forall|ii: int, jj: int|
                ((0 <= ii && ii < nums.len() && ii < jj && jj < nums.len())) ==> nums[ii] + nums[jj]
                < 256,
            nums.len() == n,
    {
        j = i + 1;
        while j < n
            invariant
                exists|ii: int, jj: int|
                    (0 <= ii && ii < jj && jj < n) && nums[ii] + nums[jj] == target,
                exists|x: int, y: int| 0 <= x && x < y && y < n && nums[x] + nums[y] == target,
                forall|jj: int| (i + 1 <= jj < j) ==> nums[(i) as int] + nums[jj] != target,
                i + 1 <= j <= n,
                i < j <= n,
                nums.len() > 1,
                forall|ii: int, jj: int|
                    ((0 <= ii && ii < nums.len() && ii < jj && jj < nums.len())) ==> nums[ii] + nums[jj]
                    < 256,
                nums.len() == n,
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

// Score: Compilation Error: False, Verified: 1, Errors: 0, Verus Errors: 0