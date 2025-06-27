
use vstd::prelude::*;
fn main() {}

verus! {

    #[verifier::loop_isolation(false)]
    fn replace_last_element(first: &Vec<i32>, second: &Vec<i32>) -> (replaced_list: Vec<i32>)
        requires
            first.len() > 0,
        ensures
            replaced_list@ == first@.subrange(0, first.len() - 1).add(second@),
    {
        let mut replaced_list = Vec::new();
        let first_end = first.len() - 1;
        let mut index = 0;
        while index < first_end
            invariant
                first.len() > 0,
                replaced_list.len() == index, // Length of replaced_list should be equal to index
                first.len() == first.len(), // Length of first does not change
                second.len() == second.len(), // Length of second does not change
                forall|i: int| 0 <= i < index ==> replaced_list[i] == first[i], // Elements copied correctly
                index <= first_end, // Ensuring index is within bounds
        {
            replaced_list.push(first[index]);
            index += 1;
        }
        index = 0;
        while index < second.len()
            invariant
                first.len() > 0,
                replaced_list.len() == first_end + index, // Ensuring replaced_list length is correct
                first.len() == first.len(), // Length of first does not change
                second.len() == second.len(), // Length of second does not change
                forall|i: int| 0 <= i < index ==> replaced_list[first_end + i] == second[i], // Elements from second copied correctly
                forall|k: int| 0 <= k < first_end ==> replaced_list[k] == first[k], // Elements copied from first are correct
                index <= second.len(), // Ensuring index is within bounds
        {
            replaced_list.push(second[index]);
            index += 1;
        }
        replaced_list
    }

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp5jutezwz`)
// 

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1
// Safe: True