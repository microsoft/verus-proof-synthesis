
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
            0 <= j <= n,
            exists|i1: int, j1: int|
                (0 <= i1 && i1 < j1 && j1 < nums.len()) && nums[i1] + nums[j1] == target,
            exists|ii: int, jj: int|
                (0 <= ii && ii < n && ii < jj && jj < n) && nums[ii] + nums[jj] == target,
            forall|ii: int, jj: int|
                ((0 <= ii && ii < i && ii < jj && jj < n) || (ii == i && ii < jj && jj < j))
                    ==> nums[ii] + nums[jj] != target,
            nums.len() > 1,
            forall|ii: int, jj: int|
                ((0 <= ii && ii < nums.len() && ii < jj && jj < nums.len())) ==> nums[ii] + nums[jj]
                    < 256,
            nums.len() == n,
            // nums is not modified in this loop, adding an invariant to cover all elements
            forall|k: int| 0 <= k < nums.len() ==> nums[k] < 256,
    {
        j = i + 1;
        while j < n
            invariant
                exists|i1: int, j1: int|
                    (0 <= i1 && i1 < j1 && j1 < nums.len()) && nums[i1] + nums[j1] == target,
                exists|ii: int, jj: int|
                    (0 <= ii && ii < n && ii < jj && jj < n) && nums[ii] + nums[jj] == target,
                forall|ii: int, jj: int|
                    ((0 <= ii && ii < i && ii < jj && jj < n) || (ii == i && ii < jj && jj < j))
                        ==> nums[ii] + nums[jj] != target,
                forall|ii: int, jj: int|
                    ((0 <= ii && ii < i && ii < jj && jj < nums.len()) || (ii == i && ii < jj && jj
                        < j)) ==> nums[ii] + nums[jj] != target,
                i < j <= n,
                nums.len() > 1,
                forall|ii: int, jj: int|
                    ((0 <= ii && ii < nums.len() && ii < jj && jj < nums.len())) ==> nums[ii] + nums[jj]
                        < 256,
                nums.len() == n,
                // nums is not modified in this loop, adding an invariant to cover all elements
                forall|k: int| 0 <= k < nums.len() ==> nums[k] < 256,
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
// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1