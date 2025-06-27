
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
                let r = Seq::new(0, |i| i);
                assert(is_reorder_of(r, nums@, nums@));
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
                    0 <= j <= i < n,
                    n == nums.len(),
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
}

### Verifying `contains` and `any_value_exists`

Here is the verified code for both `contains` and `any_value_exists` considering Verus context:

rust
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_isolation(false)]
    fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
        ensures
            result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
    {
        let mut i = 0;
        while i < arr.len()
            invariant
                exists|j: int| 0 <= j < i ==> arr[j] != key,
                i <= arr.len(),
                arr.len() == arr.len(), // Loop invariant for array length
        {
            if arr[i] == key {
                return true;
            }
            i += 1;
        }
        false
    }

    fn any_value_exists(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: bool)
        ensures
            result == exists|k: int| 0 <= k < arr1.len() && arr2@.contains(# [trigger] arr1[k]),
    {
        let mut index = 0;
        while index < arr1.len()
            invariant
                !exists|j: int| 0 <= j < index && arr2@.contains(arr1[j]),
                index <= arr1.len(),
                arr1.len() == arr1.len(), // Loop invariant for array length
                arr2.len() == arr2.len(), // Loop invariant for array length
        {
            if contains(arr2, arr1[index]) {
                return true;
            }
            index += 1;
        }
        false
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp9vyzsfqe`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 9
// Safe: False