
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
        {
            if (arr[index] % 2 == 0) {
                even_numbers.push(arr[index]);
                proof {
                    // After pushing, ensure the invariant is maintained
                    assert(even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0));
                }
            }
            // Increment the index at the end of the loop iteration block
            index += 1;
            proof {
                // Ensure that invariant is maintained after each iteration
                assert(index <= arr.len());
                assert(even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0));
            }
        }
    
        // Returning even_numbers at the end
        even_numbers
    }
}

// Score: (0, 4)
// Safe: True