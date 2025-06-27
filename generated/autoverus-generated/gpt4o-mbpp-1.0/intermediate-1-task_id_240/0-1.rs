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
            index <= first_end,
            replaced_list.len() == index,
            forall |k: int| 0 <= k < index ==> replaced_list[k] == first[k],
    {
        replaced_list.push(first[index]);
        index += 1;
    }
    
    index = 0;
    
    while index < second.len()
        invariant
            index <= second.len(),
            replaced_list.len() == first_end + index,
            forall |k: int| 0 <= k < first_end ==> replaced_list[k] == first[k],
            forall |k: int| 0 <= k < index ==> replaced_list[first_end + k] == second[k],
    {
        replaced_list.push(second[index]);
        index += 1;
    }
    
    replaced_list
}

} // verus!
// is safe: True
// Score: Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 2