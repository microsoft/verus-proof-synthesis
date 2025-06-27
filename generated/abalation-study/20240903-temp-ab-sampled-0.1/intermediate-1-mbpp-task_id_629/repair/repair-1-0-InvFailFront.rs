use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
{
    let mut even_numbers: Vec<u32> = Vec::new();
    let mut index = 0;
    proof {
        assert(even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0));
    } // Added by AI
    while index < arr.len()
        invariant
            even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0),
            index <= arr.len(),
            index < arr.len(),
            arr.len() == arr.len(),
            // The array `arr` is never modified in the loop
            forall |k: int| 0 <= k < arr.len() ==> arr[k] == arr[k],
    {
        if (arr[index] % 2 == 0) {
            even_numbers.push(arr[index]);
        }
        index += 1;
    }
    even_numbers
}

} // verus!

//             even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0),
//   None: even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0)

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 3
// Safe: True