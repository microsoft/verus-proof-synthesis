/*
Based on this Rust program.
https://github.com/TheAlgorithms/Rust/blob/master/src/backtracking/permutations.rs

Verus does not support "continue", "for", !vec, and clone.
So, I refactored the original code accordingly.

Spec and loop invariants are added to prove no buffer overflow.

No spec/invariant is needed to prove no arithmetic under/overflow.
*/

/*
The permutations problem involves finding all possible permutations
of a given collection of distinct integers. For instance, given [1, 2, 3],
the goal is to generate permutations like
 [1, 2, 3], [1, 3, 2], [2, 1, 3], [2, 3, 1], [3, 1, 2], and [3, 2, 1].
 This implementation uses a backtracking algorithm to generate all possible permutations.
*/
  
use vstd::prelude::*;

 
verus!{

    fn main() {
	    let mut v: Vec<i32> = Vec::new();
	    v.push(1);
	    v.push(2);
	    v.push(3);	
	    let permutations = permute(v);
    }

    #[verifier::external_body]
    fn myVecClone(v: &Vec<i32>) -> Vec<i32> {
	    v.clone()
    }

    pub fn permute(nums: Vec<i32>) -> Vec<Vec<i32>> {
        let mut result = Vec::new(); // Vector to store the resulting permutations
        let mut current_permutation = Vec::new(); // Vector to store the current permutation being constructed
        let mut used: Vec<bool> = Vec::new();
	
    	let mut i = 0;

	    while i < nums.len() 
        invariant
            used.len() == i,
            i <= nums.len(),
        {
		    used.push(false); // Initialize the used array to all false
		    i += 1;
	    }

        backtrack(&nums, &mut current_permutation, &mut used, &mut result); // Call the backtracking function

        result // Return the list of permutations
    }

    fn backtrack(
        nums: &Vec<i32>,
        current_permutation: &mut Vec<i32>,
        used: &mut Vec<bool>,
        result: &mut Vec<Vec<i32>>,
    ) 
    requires
        nums.len() == old(used).len(),
    ensures
        used.len() == old(used).len(),    
    {
        if current_permutation.len() == nums.len() {
            // If the current permutation is of the same length as the input,
            // it is a complete permutation, so add it to the result.
            result.push(myVecClone(current_permutation));
            return;
        }

	    let mut i = 0;
        while i < nums.len() 
        invariant 
            used.len() == nums.len(),
        {
            if used[i] {
              //  i += 1;
              //  continue; // Skip used elements
            }else{
                current_permutation.push(nums[i]); // Add the current element to the permutation
                used.set(i, true); // Mark the element as used

                backtrack(nums, current_permutation, used, result); // Recursively generate the next permutation

                current_permutation.pop(); // Backtrack by removing the last element
                used.set(i, false); // Mark the element as unused for the next iteration
            }
    		i += 1;
        }
    }
}
