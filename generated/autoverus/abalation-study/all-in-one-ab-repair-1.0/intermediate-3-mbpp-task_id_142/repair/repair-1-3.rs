
use vstd::prelude::*;
fn main() {}

verus!{

    spec fn count_identical(s1: Seq<i32>, s2: Seq<i32>, s3: Seq<i32>) -> int {
        if s1.len() == 0 || s2.len() == 0 || s3.len() == 0 {
            0
        } else {
            count_identical(s1.subrange(0, s1.len() - 1), s2.subrange(0, s2.len() - 1), s3.subrange(0, s3.len() - 1))
            + if s1.last() == s2.last() && s2.last() == s3.last() {
                1
            } else {
                0
            }
        }
    }

    fn count_identical_position(arr1: &Vec<i32>, arr2: &Vec<i32>, arr3: &Vec<i32>) -> (count: usize)
        requires
            arr1.len() == arr2.len() && arr2.len() == arr3.len(),
        ensures
            0 <= count <= arr1.len(),
            count_identical(arr1@, arr2@, arr3@) == count as int,
    {
        let n = arr1.len();
        let mut count: usize = 0;
        let mut index: usize = 0;

        while index < n
            invariant
                arr1.len() == arr2.len() && arr2.len() == arr3.len(),
                count <= index,
                index <= n,
                count_identical(
                    arr1@.subrange(0, index as int),
                    arr2@.subrange(0, index as int),
                    arr3@.subrange(0, index as int),
                ) == count as int,
                arr1.len() == arr2.len() && arr2.len() == arr3.len(), // Loop invariant added
        {
            if arr1[index] == arr2[index] && arr2[index] == arr3[index] {
                count += 1;
            }
            index += 1;
        }
        count
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp819hapeg`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False