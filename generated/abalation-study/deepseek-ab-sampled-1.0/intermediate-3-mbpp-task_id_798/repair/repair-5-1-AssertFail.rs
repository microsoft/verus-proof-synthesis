
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
            let r = Seq::new(0, |i: int| i);
            assert(is_reorder_of(r, nums@, nums@));
        }
        return;
    }
    let ghost mut r = Seq::new(nums@.len(), |i: int| i);
    proof {
        assert(is_reorder_of(r, nums@, nums@));
    }
    for i in 1..n
    invariant
        sorted_between(nums@, 0, i as int),
        is_reorder_of(r, nums@, old(nums)@),
        exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@),
    {
        let mut j = i;
        while j > 0
        invariant
            0 <= j <= i < n,
            n == nums.len(),
            j < n, // Explicitly assert j is within bounds
            sorted_between(nums@, 0, j as int),
            sorted_between(nums@, j as int, i as int + 1),
            is_reorder_of(r, nums@, old(nums)@),
            exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@),
        {
            if nums[j - 1] > nums[j] {
                let temp = nums[j - 1];
                nums.set(j - 1, nums[j]);
                nums.set(j, temp);
                proof {
                    lemma_sorted_between_single_element(nums@, j as int - 1);
                    r = r.update(j - 1, r[j as int]).update(j as int, r[j - 1]);
                }
            }
            proof {
                lemma_sorted_between_transitive(nums@, 0, j as int, i as int + 1);
            }
            j -= 1;
            proof {
                assert(is_reorder_of(r, nums@, old(nums)@));
                assert(exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@));
            }
        }
    }
}
}


//         assert(sum + arr[( index ) as int] as i128 >= i128::MIN);
//   assertion failed: sum + arr[( index ) as int] as i128 >= i128::MIN

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False