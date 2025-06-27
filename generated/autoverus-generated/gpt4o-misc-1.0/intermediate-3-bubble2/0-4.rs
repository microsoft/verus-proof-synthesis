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
            return;
        }
        for i in 1..n
            invariant
                nums.len() == n,
                0 <= i <= n,
                exists|r: Seq<int>| is_reorder_of(r.subrange(0, i as int), nums@.subrange(0, i as int), old(nums)@.subrange(0, i as int)),
        {
            let mut j = i;
            while j != 0
                invariant
                    nums.len() == n,
                    0 <= j <= i,
                    sorted_between(nums@, j as int, i as int + 1),
                    exists|r: Seq<int>| is_reorder_of(r.subrange(0, i as int + 1), nums@.subrange(0, i as int + 1), old(nums)@.subrange(0, i as int + 1)),
            {
                if nums[j - 1] > nums[j] {
                    let temp = nums[j - 1];
                    nums.set(j - 1, nums[j]);
                    nums.set(j, temp);
                }
                j -= 1;
            }
        }
    }
}

// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1