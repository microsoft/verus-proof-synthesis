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

    while index < first_end {
        replaced_list.push(first[index]);
        index += 1;
    }
    index = 0;
    while index < second.len() {
        replaced_list.push(second[index]);
        index += 1;
    }
    replaced_list
}

} // verus!
