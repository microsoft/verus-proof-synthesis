use vstd::prelude::*;

fn main() {}

verus! {

fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
{
    let mut even_numbers: Vec<u32> = Vec::new();
    let mut index = 0;
    let arr_len = arr.len();

    proof {
        // Ensure that the initial even_numbers vector is an empty filter of arr
        assert(even_numbers@ == arr@.take(0).filter(|x: u32| x % 2 == 0));
    }

    while index < arr_len 
        invariant 
            0 <= index <= arr_len,
            arr@.len() == arr_len,
            even_numbers@ == arr@.take(index as int).filter(|x: u32| x % 2 == 0),
    {
        if arr[index] % 2 == 0 {
            even_numbers.push(arr[index]);
        }
        proof {
            // Prove the invariant holds after pushing an even number
            assert(arr@.take(index as int + 1).drop_last() == arr@.take(index as int));
            reveal(Seq::filter);
        }
        index += 1;
    }
    
    proof {
        // Final proof that ensures the resulting vector is the filtered sequence
        assert(arr@ == arr@.take(arr_len as int));
    }

    even_numbers
}
} // verus!

// Score: (2, 0)
// Safe: False