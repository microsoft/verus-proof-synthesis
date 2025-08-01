
use vstd::prelude::*;
fn main() {}

verus! {
    spec fn count_identical(s1: Seq<i32>, s2: Seq<i32>, s3: Seq<i32>) -> int
        decreases s1.len()
    {
        if s1.len() == 0 || s2.len() == 0 || s3.len() == 0 {
            0
        } else {
            count_identical(s1.subrange(0, s1.len() - 1), s2.subrange(0, s2.len() - 1), s3.subrange(0, s3.len() - 1)) +
                if s1.index(s1.len() - 1) == s2.index(s2.len() - 1) && s2.index(s2.len() - 1) == s3.index(s3.len() - 1) {
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
        let mut count = 0;
        let mut index = 0;
        while index < arr1.len()
            invariant
                arr1.len() == arr2.len() && arr2.len() == arr3.len(),
                count as int <= index as int,
                index <= arr1.len(),
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
        proof {
            assert(count_identical(arr1@, arr2@, arr3@) == count as int);
        }
        count
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpl6oyugw4`)
// 

// Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 2
// Safe: True