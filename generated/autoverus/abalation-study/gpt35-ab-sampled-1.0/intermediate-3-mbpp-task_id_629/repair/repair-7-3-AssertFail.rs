
use vstd::prelude::*;
fn main() {}

verus! {

proof fn even_filter_imply_even_numbers(arr: Vec<u32>, index: u32, even_numbers: Vec<u32>)
    requires index <= arr.len(),
    ensures even_numbers@.ext_equal(arr@.subrange(0, index).filter(|x: u32| x % 2 == 0))
    decreases arr.len() - index
{
    if index < arr.len() {
        if arr[index] % 2 == 0 {
            lemma_filter_push_equality(arr@.subrange(0, index), arr[index],  |x: u32| x % 2 == 0);
            even_filter_imply_even_numbers(arr, index + 1, even_numbers.push(arr[index]));
        } else {
            lemma_filter_push_inequality(arr@.subrange(0, index), arr[index],  |x: u32| x % 2 == 0);
            even_filter_imply_even_numbers(arr, index + 1, even_numbers);
        }
    }
}

/// Helper function to assert the equality of filtered array and even numbers vector
proof fn assert_even_numbers(arr: Vec<u32>, even_numbers: Vec<u32>)
    requires even_numbers@.ext_equal(arr@.filter(|x: u32| x % 2 == 0))
    ensures even_numbers@.ext_equal(arr@.filter(|x: u32| x % 2 == 0))
{
    even_filter_imply_even_numbers(arr, 0, Vec::new());
    assert even_numbers@.ext_equal(arr@.filter(|x: u32| x % 2 == 0));
}


#[verifier::loop_isolation(false)]
fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
    ensures
        even_numbers@.ext_equal(arr@.filter(|x: u32| x % 2 == 0)),
{
    let mut even_numbers: Vec<u32> = Vec::new();
  
    assert_even_numbers(*arr, even_numbers);

    let mut index = 0;
    while index < arr.len()
        invariant
            index <= arr.len(),
            even_numbers@.ext_equal(arr@.subrange(0, index).filter(|x: u32| x % 2 == 0)),
    {
        if (arr[index] % 2 == 0) {
            even_numbers.push(arr[index]);
        }
        index += 1;
        assert_even_numbers(*arr, even_numbers);
    }
  
    assert_even_numbers(*arr, even_numbers);
  
    even_numbers
}

} // verus!


//     assert(even_numbers@ == arr@.filter(|x: u32| x % 2 == 0)); // Added by AI
//   assertion failed: even_numbers@ == arr@.filter(|x: u32| x % 2 == 0)

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False