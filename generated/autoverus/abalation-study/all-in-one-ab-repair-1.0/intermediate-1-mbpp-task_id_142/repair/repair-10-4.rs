
use vstd::prelude::*;
fn main() {}

verus! {
    spec fn count_identical(s1: Seq<i32>, s2: Seq<i32>, s3: Seq<i32>) -> int
        decreases s1.len(), s2.len(), s3.len(),
    {
        if s1.len() == 0 || s2.len() == 0 || s3.len() == 0 {
            0
        } else {
            count_identical(s1.take(s1.len() - 1), s2.take(s2.len() - 1), s3.take(s3.len() - 1)) + 
            if s1[s1.len() - 1] == s2[s2.len() - 1] && s2[s2.len() - 1] == s3[s3.len() - 1] {
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
        let mut count = 0;
        let mut index = 0;
        
        while index < arr1.len()
            invariant
                arr1.len() == arr2.len() && arr2.len() == arr3.len(),
                count <= index,
                index <= arr1.len(),
                count_identical(
                    arr1@.take(index as int),
                    arr2@.take(index as int),
                    arr3@.take(index as int),
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
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp73vat7wr`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False