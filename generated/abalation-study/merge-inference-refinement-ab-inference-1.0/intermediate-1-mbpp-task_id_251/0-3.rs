use vstd::prelude::*;

fn main() {}

verus! {

fn insert_before_each(arr: &Vec<i32>, elem: i32) -> (result: Vec<i32>)
    ensures
        result@.len() == (2 * arr.len()), // Ensure that the result has double the length of the original array
        forall|k: int| 0 <= k < arr.len() ==> #[trigger] result[2 * k] == elem, // Ensure that every even index of the result is the elem
        forall|k: int| 0 <= k < arr.len() ==> #[trigger] result[2 * k + 1] == arr[k], // Ensure that every odd index of the result is the original element
{
    let mut result: Vec<i32> = Vec::new();
    let mut index = 0;

    while index < arr.len()
        invariant
            index <= arr.len(), // The loop index must not exceed the array length
            result.len() == 2 * index, // The result length should always be double the loop index
            forall|k: int| 0 <= k < index ==> result[2 * k] == elem, // Maintain even-index invariant for processed elements
            forall|k: int| 0 <= k < index ==> result[2 * k + 1] == arr[k], // Maintain odd-index invariant for processed elements
            arr.len() == arr.len(), // Maintain unchanged array length invariant
    {
        result.push(elem);
        result.push(arr[index]);
        index += 1;
    }

    result
}

} // verus!
// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1