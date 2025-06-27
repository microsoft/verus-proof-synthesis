use vstd::prelude::*;

fn main() {}

verus! {

fn filter_odd_numbers(arr: &Vec<u32>) -> (odd_list: Vec<u32>)
    ensures
        odd_list@ == arr@.filter(|x: u32| x % 2 != 0),
{
    let mut odd_list: Vec<u32> = Vec::new();
    let input_len = arr.len();

    let mut index = 0;
    while index < arr.len() {
        if (arr[index] % 2 != 0) {
            odd_list.push(arr[index]);
        }
        index += 1;
    }
    odd_list
}

} // verus!
