
use vstd::prelude::*;
fn main() {}

verus! {
    spec fn filter_even(a: Seq<u32>) -> Seq<u32> {
        seq![for x in a if x % 2 == 0]
    }

    fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
        ensures
            even_numbers@ == filter_even(arr@),
    {
        let mut even_numbers: Vec<u32> = Vec::new();
        let mut index = 0;
        while index < arr.len()
            invariant
                even_numbers@ == filter_even(arr@.take(index as int)),
                index <= arr.len(),
                arr.len() == arr.len(),
                forall |k:int| 0 <= k < arr.len() ==> arr[k] == arr[k], // Conserving array identity
        {
            if arr[index] % 2 == 0 {
                even_numbers.push(arr[index]);
            }
            index += 1;
        }
        even_numbers
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpnptkcrcl`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False