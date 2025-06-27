
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
            replaced_list.len() == index,
            forall|k: int| 0 <= k < index ==> replaced_list[k] == first[k],
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
            forall|k: int| 0 <= k < first_end ==> replaced_list[k] == first[k],
            forall|k: int| 0 <= k < index ==> replaced_list[first_end + k] == second[k],
            index <= second.len(),
    {
        replaced_list.push(second[index]);
        index += 1;
    }
    replaced_list
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpgoxa0b1p`)
// 

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1
// Safe: True