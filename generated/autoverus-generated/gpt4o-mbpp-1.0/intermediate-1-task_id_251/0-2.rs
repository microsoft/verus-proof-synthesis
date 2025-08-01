use vstd::prelude::*;

fn main() {}

verus! {

fn insert_before_each(arr: &Vec<i32>, elem: i32) -> (result: Vec<i32>)
    ensures
        result@.len() == (2 * arr.len()),
        forall|k: int| 0 <= k < arr.len() ==> #[trigger] result[2 * k] == elem,
        forall|k: int| 0 <= k < arr.len() ==> #[trigger] result[2 * k + 1] == arr[k],
{
    let mut result: Vec<i32> = Vec::new();
    let mut index = 0;

    while index < arr.len()
        invariant
            index <= arr.len(),
            result.len() == 2 * index,
            forall |k: int| 0 <= k < index ==> result[2 * k] == elem,
            forall |k: int| 0 <= k < index ==> result[2 * k + 1] == arr[k],
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