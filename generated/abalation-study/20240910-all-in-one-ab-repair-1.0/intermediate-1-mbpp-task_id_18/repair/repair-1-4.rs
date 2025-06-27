
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
                assert(is_reorder_of(r, nums@, nums@));
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
                        let new_seq = nums@.update(j-1, nums@[j as int]).update(j as int, nums@[j-1]);
                        assert(is_reorder_of(r2, new_seq, old(nums)@));
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

    fn contains(str: &Vec<char>, key: char) -> (result: bool)
        ensures
            result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
    {
        let mut i = 0;
        while i < str.len()
            invariant
                forall|j: int| 0 <= j < i ==> str[j] != key,
                forall|k: int| 0 <= k < str.len() ==> str[k] == str[k], // Covered invariant for array str
                i <= str.len(),
                str.len() == str.len(), // Loop invariant for the array length
        {
            if str[i] == key {
                return true;
            }
            i += 1;
        }
        false
    }

    fn remove_chars(str1: &Vec<char>, str2: &Vec<char>) -> (result: Vec<char>)
        ensures
            forall|i: int|
                0 <= i < result.len() ==> (str1@.contains(#[trigger] result[i]) && !str2@.contains(#[trigger] result[i])),
            forall|i: int|
                0 <= i < str1.len() ==> (str2@.contains(#[trigger] str1[i]) || result@.contains(#[trigger] str1[i])),
    {
        let mut output_str = Vec::new();
        let mut index: usize = 0;
        while index < str1.len()
            invariant
                forall|i: int|
                    0 <= i < index ==> (str2@.contains(#[trigger] str1[i]) || output_str@.contains(#[trigger] str1[i])),
                forall|i: int|
                    0 <= i < output_str.len() ==> (str1@.contains(#[trigger] output_str[i]) && !str2@.contains(#[trigger] output_str[i])),
                forall|k: int| 0 <= k < str1.len() ==> str1[k] == str1[k], // Covered invariant for array str1
                forall|k: int| 0 <= k < str2.len() ==> str2[k] == str2[k], // Covered invariant for array str2
                index <= str1.len(),
                index == output_str.len() + (index - output_str.len()), // Added invariant for indices consistency
                str1.len() == str1.len(), // Loop invariant for the array length
                str2.len() == str2.len(), // Loop invariant for the array length
        {
            if !contains(str2, str1[index]) {
                output_str.push(str1[index]);
            }
            index += 1;
        }
        output_str
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpkynl5rbe`)
// 

// Compilation Error: False, Verified: 5, Errors: 2, Verus Errors: 2
// Safe: False