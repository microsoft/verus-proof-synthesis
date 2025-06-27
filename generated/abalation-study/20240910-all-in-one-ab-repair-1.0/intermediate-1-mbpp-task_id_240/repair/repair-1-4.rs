
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_isolation(false)]
    fn replace_last_element(first: &Vec<i32>, second: &Vec<i32>) -> Vec<i32>
        requires
            first.len() > 0,
        ensures
            result == first.subrange(0, first.len() - 1).add(second),
    {
        let mut replaced_list = Vec::new();
        let first_end = first.len() - 1;
        let mut index = 0;

        // Copy elements from first vector except the last element
        while index < first_end
            invariant
                first.len() > 0,
                first.len() == first.len(), 
                second.len() == second.len(),
                index <= first_end,
                replaced_list.len() == index,
                forall|k: int| 0 <= k < index ==> replaced_list[k] == first[k],
        {
            replaced_list.push(first[index]);
            index += 1;
        }

        // Reset index for the second vector
        index = 0;

        // Append elements from second vector to replaced_list
        while index < second.len()
            invariant
                first.len() > 0,
                first.len() == first.len(), 
                second.len() == second.len(),
                first_end + index <= replaced_list.len() <= first_end + second.len(),
                forall|k: int| 0 <= k < first_end ==> replaced_list[k] == first[k],
                forall|k: int| 0 <= k < index ==> replaced_list[first_end + k] == second[k],
        {
            replaced_list.push(second[index]);
            index += 1;
        }

        replaced_list
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpl8lj2x9x`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False