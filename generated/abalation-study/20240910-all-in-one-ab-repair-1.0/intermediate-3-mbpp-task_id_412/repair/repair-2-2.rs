
use vstd::prelude::*;
fn main() {}

verus! {

    spec fn filter_even(arr: Seq<u32>) -> Seq<u32> {
        arr.filter(|x: u32| x % 2 == 0)
    }

    fn remove_odds(arr: &Vec<u32>) -> (even_list: Vec<u32>)
        ensures
            even_list@ == filter_even(arr@),
    {
        let mut even_list: Vec<u32> = Vec::new();
        let input_len = arr.len();
        let mut index = 0;

        while index < arr.len()
            invariant
                even_list@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0),
                index <= arr.len(),
                arr.len() == input_len,
                even_list.len() <= index,
        {
            if arr[index] % 2 == 0 {
                even_list.push(arr[index]);
            }
            index += 1;
        }
        even_list
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpffw56cke`)
// 

// Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 3
// Safe: False