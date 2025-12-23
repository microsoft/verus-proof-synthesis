
use vstd::prelude::*;
fn main() {}

verus! {
    spec fn is_even(x: u32) -> bool {
        x % 2 == 0
    }

    fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
        ensures
            even_numbers@ == arr@.filter(|x: u32| is_even(x)),
    {
        let mut even_numbers: Vec<u32> = Vec::new();
        let mut index = 0;
        while index < arr.len()
            invariant
                even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| is_even(x)),
                index <= arr.len(),
        {
            if arr[index] % 2 == 0 {
                even_numbers.push(arr[index]);
                proof {
                    let old_even_numbers = even_numbers@.subrange(0, even_numbers.len() as int - 1);
                    let new_even_number = Seq::new(1, |_: int| arr[index]);
                    let updated_even_numbers = old_even_numbers.add(new_even_number);

                    assert(even_numbers@.len() == updated_even_numbers.len());
                    assert(even_numbers@ == updated_even_numbers);
                }
            }
            index += 1;
            proof {
                let subrange_filtered = arr@.subrange(0, index as int).filter(|x: u32| is_even(x));
                assert(even_numbers@ == subrange_filtered);
            }
        }

        // Returning even_numbers at the end
        even_numbers
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpgp0alpy3`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False