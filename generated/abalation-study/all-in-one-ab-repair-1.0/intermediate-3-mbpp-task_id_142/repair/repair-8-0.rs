
use vstd::prelude::*;
fn main() {}

verus! {
    // A specification function to count identical positions in three sequences.
    spec fn count_identical(s1: Seq<i32>, s2: Seq<i32>, s3: Seq<i32>) -> int
        decreases s1.len(), s2.len(), s3.len()
    {
        if s1.len() == 0 || s2.len() == 0 || s3.len() == 0 {
            0
        } else {
            // Recursively count identical positions.
            count_identical(s1.drop_last(), s2.drop_last(), s3.drop_last()) + 
            if s1.last() == s2.last() && s2.last() == s3.last() {
                1 as int
            } else {
                0 as int
            }
        }
    }

    // Function to count identical positions in three vectors.
    fn count_identical_position(arr1: &Vec<i32>, arr2: &Vec<i32>, arr3: &Vec<i32>) -> (count: usize)
        requires
            arr1.len() == arr2.len() && arr2.len() == arr3.len(), // Ensure all arrays are the same length.
        ensures
            0 <= count <= arr1.len(), // Count is within valid range.
            count_identical(arr1@, arr2@, arr3@) == count, // The count matches the specification.
    {
        let mut count = 0;
        let mut index = 0;
        while index < arr1.len()
            invariant
                arr1.len() == arr2.len() && arr2.len() == arr3.len(), // Arrays remain of equal length.
                count <= index, // Count is always less than or equal to the index.
                index <= arr1.len(), // Index is within the range of the array.
                count_identical(
                    arr1@.subrange(0, index as int),
                    arr2@.subrange(0, index as int),
                    arr3@.subrange(0, index as int),
                ) == count as int, // Count matches the number of identical positions so far.
        {
            if arr1[index] == arr2[index] && arr2[index] == arr3[index] {
                count += 1;
            }
            index += 1;
        }
        count
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp49d6y1zr`)
// 

// Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 2
// Safe: True