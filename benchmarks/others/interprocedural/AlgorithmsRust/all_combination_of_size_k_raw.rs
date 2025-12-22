use vstd::prelude::*;

 
verus!{

	fn main() {
		
		let res = generate_all_combinations(4, 2);

	}

	fn myVecClone(v: &Vec<i32>) -> Vec<i32> {
        let mut ret : Vec<i32> = vec![];

        let mut i = 0;
        while i < v.len(){
            ret.push(v[i]);
        }
        ret
	}

	pub fn generate_all_combinations(n: i32, k: i32) -> Vec<Vec<i32>> 
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
	{
		
		if level == 0 {
			total_list.push(myVecClone(current_list));
			return;
		}
	
		let mut i = increment;

		while i < total_number - level + 2 
		{
			current_list.push(i);
			create_all_state(i + 1, total_number, level - 1, current_list, total_list);
			current_list.pop();
			i += 1;
		}
	}
}
     
