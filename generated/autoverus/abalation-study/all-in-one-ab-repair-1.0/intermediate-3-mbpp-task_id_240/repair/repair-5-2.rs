
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

        // Loop to copy elements from first to replaced_list up to first_end
        while index < first_end
            invariant
                first.len() > 0,
                index <= first_end,
                replaced_list.len() == index,
                forall|i: int| 0 <= i < index ==> replaced_list@[i] == first@[i],
        {
            replaced_list.push(first[index]);
            index += 1;
        }

        index = 0;

        // Loop to copy all elements from second to replaced_list
        while index < second.len()
            invariant
                first.len() > 0,
                index <= second.len(),
                replaced_list.len() == first_end + index,
                forall|i: int| 0 <= i < first_end ==> replaced_list@[i] == first@[i],
                forall|k: int| 0 <= k < index ==> replaced_list@[first_end + k] == second@[k],
        {
            replaced_list.push(second[index]);
            index += 1;
        }

        proof {
            let replaced_seq = first@.subrange(0, first_end as int).add(second@);
            assert(replaced_list@ == replaced_seq);
        }

        replaced_list
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmplcs2dnci`)
// 

// Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 1
// Safe: True