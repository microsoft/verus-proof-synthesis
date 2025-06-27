
use vstd::prelude::*;
fn main() {}

verus! {
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
                replaced_list.len() == index,
                first_end == first.len() - 1,
                second.len() == second.len(),
                index <= first_end,
                forall|i: int| 0 <= i < index ==> replaced_list[i] == first[i] as i32,
        {
            replaced_list.push(first[index]);
            index += 1;
        }

        // Added assertion to maintain invariant just before the second while loop
        assert(replaced_list.len() == first_end);

        index = 0;

        while index < second.len()
            invariant
                first.len() > 0,
                replaced_list.len() == first_end + index,
                first_end == first.len() - 1,
                second.len() == second.len(),
                forall|i: int| 0 <= i < index ==> replaced_list[first_end + i] == second[i] as i32,
                forall|k: int| 0 <= k < first_end ==> replaced_list[k] == first[k] as i32,
                index <= second.len(),
        {
            replaced_list.push(second[index]);
            index += 1;
        }

        replaced_list
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmptlt59__n`)
// 

// Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 1
// Safe: True