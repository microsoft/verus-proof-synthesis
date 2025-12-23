
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::external_body]
    spec fn filter_even(seq: Seq<u32>) -> Seq<u32> {
        seq.filter(|x: &u32| *x % 2 == 0)
    }

    fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
        ensures
            even_numbers@ == filter_even(arr@),
    {
        let mut even_numbers: Vec<u32> = Vec::new();
        let mut index = 0;
        while index < arr.len()
            invariant
                even_numbers@ == arr@
                    .subrange(0, index as int)
                    .filter(|x: &u32| *x % 2 == 0),
                index <= arr.len(),
                arr.len() == arr.len(),
        {
            if arr[index] % 2 == 0 {
                even_numbers.push(arr[index]);
            }
            index += 1;
        }
        even_numbers
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpdud2pgh5`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False