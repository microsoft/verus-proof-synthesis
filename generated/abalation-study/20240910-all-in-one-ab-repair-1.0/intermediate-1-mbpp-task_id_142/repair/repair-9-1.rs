
use vstd::prelude::*;
fn main() {}

verus! {
    spec fn count_identical(s1: Seq<i32>, s2: Seq<i32>, s3: Seq<i32>) -> int
        decreases s1.len(), s2.len(), s3.len(),
    {
        if s1.len() == 0 || s2.len() == 0 || s3.len() == 0 {
            0
        } else {
            count_identical(s1.drop_last(), s2.drop_last(), s3.drop_last()) + 
            if s1.last() == s2.last() && s2.last() == s3.last() {
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
            count_identical(arr1@, arr2@, arr3@) == count as int,
    {
        let n = arr1.len();
        let mut count = 0;
        let mut index = 0;
        
        while index < n
            invariant
                arr1.len() == n && arr2.len() == n && arr3.len() == n,
                0 <= index <= n,
                0 <= count <= index,
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
            let expected_count = count_identical(arr1@, arr2@, arr3@);
            assert(expected_count == count as int);
        }

        count
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmppzlu0cph`)
// 

// Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 2
// Safe: False