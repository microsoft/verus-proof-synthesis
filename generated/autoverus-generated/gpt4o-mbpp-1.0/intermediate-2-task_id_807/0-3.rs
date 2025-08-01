use vstd::prelude::*;

fn main() {}

verus! {

fn find_first_odd(arr: &Vec<u32>) -> (index: Option<usize>)
    ensures
        if let Some(idx) = index {
            &&& arr@.take(idx as int) == arr@.take(idx as int).filter(|x: u32| x % 2 == 0)
            &&& arr[idx as int] % 2 != 0
        } else {
            forall|k: int| 0 <= k < arr.len() ==> (arr[k] % 2 == 0)
        },
{
    let input_len = arr.len();
    let mut index = 0;
    while index < arr.len()
        invariant
            index <= arr.len(),
            arr.len() == input_len,
            arr@ == old(arr@),
            forall|k: int| 0 <= k < index ==> arr[k] % 2 == 0,
    {
        if (arr[index] % 2 != 0) {
            return Some(index);
        }
        index += 1;
    }
    None
}

} // verus!
// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1