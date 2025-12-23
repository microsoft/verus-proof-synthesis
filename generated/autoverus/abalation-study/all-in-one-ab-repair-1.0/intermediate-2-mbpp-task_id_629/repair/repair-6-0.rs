
use vstd::prelude::*;
fn main() {}

verus! {
    spec fn filter_even(a: Seq<u32>) -> Seq<u32> {
        a.filter(|x: u32| x % 2 == 0)
    }

    #[verifier::loop_invariant]
    fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
        ensures
            even_numbers@ == filter_even(arr@),
    {
        let mut even_numbers: Vec<u32> = Vec::new();
        let mut index = 0;
        while index < arr.len()
            invariant
                even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0),
                index <= arr.len(),
                arr.len() == arr.len(),
        {
            if arr[index] % 2 == 0 {
                even_numbers.push(arr[index]);
                proof {
                    let sub_seq = arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0);
                    assert(even_numbers@.subrange(0, even_numbers.len() - 1) == sub_seq);
                    assert(even_numbers@ == sub_seq.push(arr[index]));
                }
            }
            index += 1;
        }
        even_numbers
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpm5p7zeis`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False