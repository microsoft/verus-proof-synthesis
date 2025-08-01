

use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun1(x: &Vec<u64>) -> (res: u64) 
    requires 
        x.len() >= 1,
    ensures
        forall |i:int| 0 <= i < x.len() ==> res >= x[i],
        exists |i:int| 0 <= i < x.len() && res == x[i],
{
    // Assert that the vector x has at least one element, as specified.
    assert(x.len() >= 1);
    
    // Initialize max_value to the first element of x.
    let mut max_value = x[0];
    
    // Initialize the loop counter i to 1.
    let mut i: usize = 1;
    
    // Capture the length of x to ensure it remains consistent throughout the loop.
    let xlen: usize = x.len();

    // Loop through each element of the vector starting from the second element (index 1).
    while (i < xlen)
        // The invariant ensures the correctness of max_value after each iteration.
        invariant
            // The current index i must be less than or equal to the length of x.
            i <= xlen,

            // Ensure that x has not been modified during the loop.
            x.len() == xlen,

            // For all elements processed so far (from 0 to i-1), max_value is the maximum.
            forall |j: int| 0 <= j < i as int ==> max_value >= x[j as int],
        {
            // If the current element x[i] is greater than max_value, update max_value.
            if x[i] > max_value {
                max_value = x[i];
            }

            // Increment the loop counter.
            i = i + 1;
        }

    // After the loop completes, max_value is the greatest element in the vector.
    max_value
}
}

// is safe: True
// Score: Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 1