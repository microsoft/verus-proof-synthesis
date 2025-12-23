
use vstd::prelude::*;
fn main() {}

verus! {
    spec fn sorted_between(a: Seq<u32>, from: int, to: int) -> bool {
        forall |i: int, j:int| from <= i < j < to ==> a[i] <= a[j]
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

        proof {
            assert(sorted_between(nums@, 0, nums@.len() as int));
            assert(exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@));
        }
    }
}

### Reviewing `remove_all_greater`

Now let's examine the `remove_all_greater` function and correct any issues:

rust
use vstd::prelude::*;
fn main() {}

verus! {

    #[verifier::loop_isolation(false)]
    pub fn remove_all_greater(v: Vec<i32>, e: i32) -> (result: Vec<i32>)
        requires
            forall|k1: int, k2: int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2], // elements are unique
        ensures
            forall|k: int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]), // all elements in output are <= e and from v
            forall|k: int| 0 <= k < v.len() && v[k] <= e ==> result@.contains(v[k]), // all elements from v that are <= e are in result
    {
        let mut i: usize = 0;
        let vlen = v.len();
        let mut result: Vec<i32> = vec![];
        while i < v.len()
            invariant
                v.len() == vlen, // len of v does not change
                result.len() <= i, // len of result is always <= i
                forall|k: int| 0 <= k < i && v[k] <= e ==> result@.contains(v[k]), // all elements in v from 0 to i that are <= e are in result
                forall|k: int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]), // all elements in result are from v and <= e
                i <= v.len(), // i is always within the range of v
                forall|k1: int, k2: int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2], // elements in v are unique,
        {
            if v[i] <= e {
                result.push(v[i]);
            }
            i = i + 1;
        }

        proof {
            assert(forall|k: int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k])); // Added by AI
            assert(forall|k: int| 0 <= k < v.len() && v[k] <= e ==> result@.contains(v[k])); // Added by AI
        }

        result
    }

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpvqjfpxik`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 6
// Safe: False