
use vstd::prelude::*;
fn main() {}

verus! {
    spec fn even_filter(a: Seq<u32>) -> Seq<u32> {
        a.filter(|x: u32| x % 2 == 0)
    }

    fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
        ensures
            even_numbers@ == even_filter(arr@),
    {
        let mut even_numbers: Vec<u32> = Vec::new();
        let mut index = 0;
        while index < arr.len()
            invariant
                even_numbers@ == even_filter(arr@.subrange(0, index as int)),
                index <= arr.len(),
                // No need to assert further properties as these cover the invariants
        {
            if arr[index] % 2 == 0 {
                even_numbers.push(arr[index]);
            }
            index += 1;
        }
        even_numbers
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp7dklaehe`)
// 

// Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 3
// Safe: False