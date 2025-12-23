
use vstd::prelude::*;
fn main() {}

verus! {
    fn replace_last_element(first: &Vec<i32>, second: &Vec<i32>) -> (replaced_list: Vec<i32>)
        requires
            first.len() > 0,
        ensures
            replaced_list@ == first@.subrange(0, first.len() as int - 1).add(second@),
    {
        let mut replaced_list = Vec::new();
        let first_end = first.len() - 1;
        let mut index = 0;
        while index < first_end
            invariant
                first.len() > 0,
                replaced_list.len() == index,
                first.len() == first.len(),
                second.len() == second.len(),
                forall|i: int| 0 <= i < index as int ==> replaced_list[i] == first[i],
                index <= first_end,
        {
            replaced_list.push(first[index]);
            index += 1;
        }

        index = 0;
        while index < second.len()
            invariant
                first.len() > 0,
                replaced_list.len() == first_end + index,
                first.len() == first.len(),
                second.len() == second.len(),
                forall|i: int| 0 <= i < first_end as int ==> replaced_list[i] == first[i],
                forall|k: int| 0 <= k < index as int ==> replaced_list[first_end + k] == second[k],
                index <= second.len(),
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


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpwyyvu4zp`)
// 

// Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 1
// Safe: False