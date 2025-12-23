
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
                let r = Seq::new(nums@.len(), |i: int| i);
                assert(is_reorder_of(r, nums@, nums@)); // Ensuring postcondition
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
                    0 <= j <= i,
                    n == nums.len(),
                    forall|x: int, y: int| 0 <= x <= y < i ==> x != j && y != j ==> nums[x] <= nums[y],
                    sorted_between(nums@, j as int, i as int + 1),
                    exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@),
            {
                if nums[j - 1] > nums[j] {
                    proof {
                        let r1 = choose|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@);
                        let r2 = r1.update(j as int - 1, r1[j as int]).update(j as int, r1[j as int - 1]);
                        assert(is_reorder_of(r2, nums@.update(j as int - 1, nums@[j as int]).update(j as int, nums@[j as int - 1]), old(nums)@));
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

    fn contains(str: &Vec<i32>, key: i32) -> (result: bool)
        ensures
            result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
    {
        let mut i = 0;
        while i < str.len()
            invariant
                forall|j: int| 0 <= j < i ==> str[j] != key,
                i <= str.len(),
                key >= i32::MIN,
                key <= i32::MAX,
                str.len() == str.len(),
        {
            if str[i] == key {
                return true;
            }
            i += 1;
        }
        false
    }

    fn remove_elements(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
        ensures
            forall|i: int|
                0 <= i < result.len() ==> (arr1@.contains(#[trigger] result[i]) && !arr2@.contains(#[trigger] result[i])),
            forall|i: int|
                0 <= i < arr1.len() ==> (arr2@.contains(#[trigger] arr1[i]) || result@.contains(#[trigger] arr1[i])),
    {
        let mut output_str = Vec::new();
        let mut index: usize = 0;
        while index < arr1.len()
            invariant
                forall|j: int|
                    0 <= j < index ==> (arr2@.contains(#[trigger] arr1[j]) || output_str@.contains(#[trigger] arr1[j])),
                forall|j: int|
                    0 <= j < output_str.len() ==> (arr1@.contains(#[trigger] output_str[j]) && !arr2@.contains(#[trigger] output_str[j])),
                index <= arr1.len(),
                output_str.len() <= index,
                arr1.len() >= 0,
                arr1.len() <= usize::MAX,
                arr2.len() >= 0,
                arr2.len() <= usize::MAX,
                arr1.len() == arr1.len(),
                arr2.len() == arr2.len(),
        {
            if !contains(arr2, arr1[index]) {
                output_str.push(arr1[index]);
            }
            index += 1;
        }
        output_str
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp2okzhn2z`)
// 

// Compilation Error: False, Verified: 4, Errors: 3, Verus Errors: 7
// Safe: False