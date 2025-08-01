
use vstd::prelude::*;
fn main() {}
verus! {

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

#[verifier::loop_isolation(false)]
pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
    requires
        forall|k: int| k <= #[trigger] b[k] <= k + 1,
        old(a).len() == N,
        b.len() == N,
        N <= 0x3FFF_FFFF,
    ensures
        N <= sum <= 2 * N,
{
    let mut i: usize = 0;
    let mut sum: i32 = 0;
    while (i < N as usize)
        invariant
            N <= 0x3FFF_FFFF,
            b.len() == N,
            forall|k: int| 0 <= k < i ==> a[k as int] == b[k as int] + 1 - k,
            i <= N as usize,
            old(a).len() == N,
            sum <= 2 * (i as i32),
            a.len() == N, // invariant added
    {
        a.set(i, b[i] + 1);
        let mut j: usize = 0;
        while (j < i)
            invariant
                N <= 0x3FFF_FFFF,
                b.len() == N,
                a[i as int] == b[i as int] + 1 - j,
                forall|k: int| 0 <= k < i ==> a[k as int] == b[k as int] + 1 - k, // covering all elements due to no a.set() in loop
                j <= i,
                old(a).len() == N,
                a.len() == N, // invariant added
        {
            a.set(i, a[i] - 1);
            j = j + 1;
        }
        sum = sum + a[i];
        i = i + 1;
    }
    sum
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp6hee074z`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 10
// Safe: False