/*
This is based on the following Rust program.
https://github.com/TheAlgorithms/Rust/blob/master/src/backtracking/all_combination_of_size_k.rs

This program actually does have arithmetic overflow problems.
I had to add these two pre-conditions for its key API function generate_all_combinations to make sure there is no overflow.
		0 <= n <= i32::MAX - 1,
		0 <= k <= n,

I put the original head comments next.
*/

/*
    In this problem, we want to determine all possible combinations of k
    numbers out of 1 ... n. We use backtracking to solve this problem.
    Time complexity: O(C(n,k)) which is O(n choose k) = O((n!/(k! * (n - k)!)))

    generate_all_combinations(n=4, k=2) => [[1, 2], [1, 3], [1, 4], [2, 3], [2, 4], [3, 4]]
*/

use vstd::prelude::*;

 
verus!{

	fn main() {
		
		let res = generate_all_combinations(4, 2);

	}

	#[verifier::external_body]
	fn myVecClone(v: &Vec<i32>) -> Vec<i32> {
		v.clone()
	}

	pub fn generate_all_combinations(n: i32, k: i32) -> Vec<Vec<i32>> 
	requires
		0 <= n <= i32::MAX - 1,
		0 <= k <= n,
	{
		let mut result = vec![];
		let mut current_list = vec![];
		create_all_state(1, n, k, &mut current_list, &mut result);
	
		result
	}
	
	fn create_all_state
	(
		increment: i32,
		total_number: i32,
		level: i32,
		current_list: &mut Vec<i32>,
		total_list: &mut Vec<Vec<i32>>,
	) 
	requires
		increment >= 1,
		0<= level <= total_number,
		total_number +1 <= i32::MAX,
	{
		
		if level == 0 {
			total_list.push(myVecClone(current_list));
			return;
		}
	
		let mut i = increment;
		while i < total_number - level + 2 
		invariant 
			i >= 1,
			1 <= level <= total_number,
			total_number +1 <= i32::MAX,
		{
			current_list.push(i);
			create_all_state(i + 1, total_number, level - 1, current_list, total_list);
			current_list.pop();
			i += 1;
		}
	}
}
     
