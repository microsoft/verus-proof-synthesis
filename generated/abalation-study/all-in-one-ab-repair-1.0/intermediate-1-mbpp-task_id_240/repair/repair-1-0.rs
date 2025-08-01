
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
            first.len() == first.len(), 
            second.len() == second.len(),
            forall|i: int| 0 <= i < index ==> replaced_list[i] == first[i],
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
            forall|i: int| 0 <= i < index ==> replaced_list[first_end + i] == second[i],
            forall|k: int| 0 <= k < first_end ==> replaced_list[k] == first[k],
            index <= second.len(),
    {
        replaced_list.push(second[index]);
        index += 1;
    }

    proof {
        // Post-condition proof: Verify that `replaced_list` is a concatenation of the subrange and the second list
        let ghost replaced_list_seq = replaced_list@;
        assert(replaced_list_seq.len() == first_end + second.len());
        forall(|i: int| 0 <= i < first_end ==> replaced_list_seq[i] == first@[i]);
        forall(|i: int| 0 <= i < second.len() ==> replaced_list_seq[first_end + i] == second@[i]);
        assert(replaced_list_seq == first@.subrange(0, first_end).add(second@));
    }

    replaced_list
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpwwt9mu1v`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: True