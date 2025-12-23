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
        0 <= index <= first_end,
        replaced_list.len() == index,
        forall|i: int| 0 <= i < index ==> replaced_list[i] == first[i],
    {
        replaced_list.push(first[index]);
        index += 1;
    }

    index = 0;
    let replaced_list_len_after_first = replaced_list.len();
    let second_len = second.len();

    while index < second_len
    invariant
        0 <= index <= second_len,
        replaced_list.len() == replaced_list_len_after_first + index,
        forall|i: int| 0 <= i < index ==> replaced_list[replaced_list_len_after_first + i] == second[i],
        forall|i: int| 0 <= i < replaced_list_len_after_first ==> replaced_list[i] == first[i],
    {
        replaced_list.push(second[index]);
        index += 1;
    }

    replaced_list
}

} // verus!

// Score: (0, 3)
// Safe: False