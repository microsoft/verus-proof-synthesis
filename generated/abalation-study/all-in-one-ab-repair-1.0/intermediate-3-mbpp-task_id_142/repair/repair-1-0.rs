
use vstd::prelude::*;
fn main() {}

verus! {
    spec fn count_identical(s1: Seq<i32>, s2: Seq<i32>, s3: Seq<i32>) -> int
    decreases s1.len(), s2.len(), s3.len(),
    {
        if s1.len() == 0 || s2.len() == 0 || s3.len() == 0 {
            0
        } else {
            count_identical(s1.drop_last(), s2.drop_last(), s3.drop_last()) + if (s1.last() == s2.last() && s2.last() == s3.last()) {
                1 as int
            } else {
                0 as int
            }
        }
    }

    fn count_identical_position(arr1: &Vec<i32>, arr2: &Vec<i32>, arr3: &Vec<i32>) -> (count: usize)
    requires
        arr1.len() == arr2.len() && arr2.len() == arr3.len(),
    ensures
        0 <= count <= arr1.len(),
        count_identical(arr1@, arr2@, arr3@) == count,
    {
        let n = arr1.len();
        let mut count = 0;
        let mut index = 0;
        while index < n
            invariant
                arr1.len() == n,
                arr2.len() == n,
                arr3.len() == n,
                count <= index,
                index <= n,
                count_identical(
                    arr1@.subrange(0, index as int),
                    arr2@.subrange(0, index as int),
                    arr3@.subrange(0, index as int),
                ) == count as int,
        {
            if arr1[index] == arr2[index] && arr2[index] == arr3[index] {
                count += 1;
            }
            index += 1;
        }
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp3e0ri02q`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False