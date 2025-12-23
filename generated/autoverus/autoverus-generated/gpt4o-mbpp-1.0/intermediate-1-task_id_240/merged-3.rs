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
            forall|i: int| 0 <= i < index ==> replaced_list[i] == first[i],
            forall|k: int| 0 <= k < index ==> replaced_list[k] == first[k],
            index <= first_end,
            replaced_list.len() == index,
            replaced_list@ == first@.subrange(0, (index) as int),
    {
        replaced_list.push(first[index]);
        index += 1;
    }
    index = 0;
    while index < second.len()
        invariant
            forall|i: int| 0 <= i < index ==> replaced_list[first_end + i] == second[i],
            forall|k: int| 0 <= k < first_end ==> replaced_list[k] == first[k],
            forall|k: int| 0 <= k < index ==> replaced_list[first_end + k] == second[k],
            forall|k: int|
                first_end <= k < first_end + index ==> replaced_list[k] == second[k - first_end],
            index <= second.len(),
            replaced_list.len() == first_end + index,
            replaced_list@ == first@.subrange(0, (first_end) as int).add(
                second@.subrange(0, (index) as int),
            ),
    {
        replaced_list.push(second[index]);
        index += 1;
    }
    replaced_list
}

} // verus!


// Score: Compilation Error: False, Verified: 0, Errors: 3, Verus Errors: 6