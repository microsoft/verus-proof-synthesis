use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

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
            arr.len() == input_len,
            forall|k: int| 0 <= k < arr.len() ==> (k < index ==> (arr[k] % 2 == 0)), // The array `arr` is never changed in the loop.
            index <= arr.len(),
    {
        if (arr[index] % 2 != 0) {
            proof {
                assert(arr@.take(index as int) == arr@.take(index as int).filter(|x: u32| x % 2 == 0)); // Added by AI
                assert(arr[index as int] % 2 != 0); // Added by AI
            }
            return Some(index);
        }
        index += 1;
    }
    None
}

} // verus!

// failed this postcondition
//         if let Some(idx) = index {
//             return Some(index);
//   at this exit: return Some(index)
//   failed this postcondition: Some(idx)

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1
// Safe: True