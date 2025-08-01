use vstd::prelude::*;

fn main() {}

verus! {

fn find_negative_numbers(arr: &Vec<i32>) -> (negative_list: Vec<i32>)
    ensures
        negative_list@ == arr@.filter(|x: i32| x < 0),
{
    let mut negative_list: Vec<i32> = Vec::new();
    let mut index = 0;

    while index < arr.len()
        invariant
            index <= arr.len(),
            negative_list@ == arr@.subrange(0, index as int).filter(|x: i32| x < 0),
    {
        if (arr[index] < 0) {
            negative_list.push(arr[index]);
        }
        index += 1;
    }

    negative_list
}

} // verus!
// is safe: True
// Score: Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 3