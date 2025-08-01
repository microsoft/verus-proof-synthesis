
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
            assert(Seq::empty().filter(|x: u32| x % 2 == 0).len() == 0);
        }
        assert(even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0));
    } // Added by AI
    while index < arr.len()
        invariant
            even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0),
            index <= arr.len(),
    {
        if (arr[index] % 2 == 0) {
            even_numbers.push(arr[index]);
        }
        index += 1;
        proof {
            assert(even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0)) by {
            }
        } // Added by AI
    }
    even_numbers
}
} // verus!


// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1