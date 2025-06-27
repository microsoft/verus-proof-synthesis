
use vstd::prelude::*;
fn main() {}

verus! {

fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
{
    let mut even_numbers: Vec<u32> = Vec::new();
    let mut index = 0;
    while index < arr.len()
        invariant
            even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0),
            index <= arr.len(),
            arr.len() == old(arr.len()),
    {
        if arr[index] % 2 == 0 {
            even_numbers.push(arr[index]);
            proof {
                // Proof that adding an even element maintains the invariant
                let even = arr[index];
                assert(even % 2 == 0);
                assert(even_numbers@.push(even) ==
                    if even_numbers.len() as int == even_numbers@.len() {
                        // Handles the case when even_numbers is not updated
                        even_numbers@
                    } else {
                        // Handles the case when even_numbers is updated
                        even_numbers@.add(seq![even])
                    }
                );
            }
        }
        index += 1;
        proof {
            assert(even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0));
        }
    }

    even_numbers
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp0bzseee4`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False