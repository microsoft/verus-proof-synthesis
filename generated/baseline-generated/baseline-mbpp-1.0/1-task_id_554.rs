use vstd::prelude::*;

fn main() {}

verus! {

fn find_odd_numbers(arr: &Vec<u32>) -> (odd_numbers: Vec<u32>)
    ensures
        odd_numbers@ == arr@.filter(|x: u32| x % 2 != 0),
{
    let mut odd_numbers: Vec<u32> = Vec::new();
    let input_len = arr.len();

    let mut index = 0;
    
    proof {
        // Initial proof block.
        assert(odd_numbers@.len() == 0);
        assert(odd_numbers@ == arr@.take(0).filter(|x: u32| x % 2 != 0));
    } // Added by AI
    
    while index < arr.len()
        invariant 
            0 <= index <= arr.len(),
            odd_numbers@ == arr@.take(index as int).filter(|x: u32| x % 2 != 0), // Ensures partial correctness regarding odd_numbers
            arr.len() == input_len,
    {
        if (arr[index] % 2 != 0) {
            odd_numbers.push(arr[index]);
        }

        proof {
            reveal(Seq::filter);
        } // Added by AI
        
        index += 1;
    }

    proof {
        // Final proof block.
        assert(arr@ == arr@.take(arr.len() as int));
        assert(odd_numbers@ == arr@.filter(|x: u32| x % 2 != 0));
    } // Added by AI
    
    odd_numbers
}

} // verus!
// Score: (1, 1)
// Safe: True