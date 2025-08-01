
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
                let r = Seq::new(0, |i: int| i);  // Added for empty vector
                assert(is_reorder_of(r, nums@, nums@)); // Added by AI
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
    fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
        ensures
            result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
    {
        let mut index = 0;
        while index < arr.len()
            invariant
                exists|k: int| 0 <= k < index ==> arr[k] != key,
                index <= arr.len(),
                arr.len() == arr.len(),   // Loop invariant specifying the length of the array
        {
            if arr[index] == key {
                return true;
            }
            index += 1;
        }
        false
    }

    fn find_dissimilar(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
        ensures
            forall|i: int|
                0 <= i < arr1.len() ==> (!arr2@.contains(#[trigger] arr1[i]) ==> result@.contains(
                    arr1[i],
                )),
            forall|i: int|
                0 <= i < arr2.len() ==> (!arr1@.contains(#[trigger] arr2[i]) ==> result@.contains(
                    arr2[i],
                )),
            forall|i: int, j: int|
                0 <= i < j < result.len() ==> #[trigger] result[i] != #[trigger] result[j],
    {
        let mut result = Vec::new();
        let mut index = 0;
        while index < arr1.len()
            invariant
                forall|i: int|
                    0 <= i < index ==> (!arr2@.contains(#[trigger] arr1[i]) ==> result@.contains(
                        arr1[i],
                    )),
                forall|k: int, l: int|
                    0 <= k < l < result.len() ==> #[trigger] result[k] != #[trigger] result[l],
                index <= arr1.len(),
                arr1.len() == arr1.len(), // Loop invariant specifying the length of arr1
                result.len() == result.len(), // Loop invariant specifying the length of result
        {
            if !contains(arr2, arr1[index]) && !contains(&result, arr1[index]) {
                result.push(arr1[index]);
            }
            index += 1;
        }
        let mut index = 0;
        while index < arr2.len()
            invariant
                forall|i: int|
                    0 <= i < arr1.len() ==> (!arr2@.contains(#[trigger] arr1[i]) ==> result@.contains(
                        arr1[i],
                    )),
                forall|i: int|
                    0 <= i < index ==> (!arr1@.contains(#[trigger] arr2[i]) ==> result@.contains(
                        arr2[i],
                    )),
                forall|k: int, l: int|
                    0 <= k < l < result.len() ==> #[trigger] result[k] != #[trigger] result[l],
                index <= arr2.len(),
                arr2.len() == arr2.len(), // Loop invariant specifying the length of arr2
                result.len() == result.len(), // Loop invariant specifying the length of result
        {
            if !contains(arr1, arr2[index]) && !contains(&result, arr2[index]) {
                result.push(arr2[index]);
            }
            index += 1;
        }
        result
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpu_3pxlco`)
// 

// Compilation Error: False, Verified: 3, Errors: 4, Verus Errors: 6
// Safe: False