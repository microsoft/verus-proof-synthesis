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
            negative_list.len() <= index,
            forall |k:int| 0 <= k < index && arr[k] < 0 ==> exists |m: int| 0 <= m < negative_list.len() && negative_list[m] == arr[k],
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
// Score: Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 2