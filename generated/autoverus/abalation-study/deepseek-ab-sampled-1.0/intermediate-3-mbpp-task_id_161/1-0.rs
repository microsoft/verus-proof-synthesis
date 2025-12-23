
use vstd::prelude::*;

fn main() {}

verus! {

fn contains(str: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
{
    let mut i = 0;
    while i < str.len()
        invariant
            i <= str.len(),
            str.len() == old(str).len(),
            forall |k: int| 0 <= k < i ==> str[k] != key,
    {
        if (str[i] == key) {
            return true;
        }
        i += 1;
    }
    false
}

fn remove_elements(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        forall|i: int|
            0 <= i < result.len() ==> (arr1@.contains(#[trigger] result[i]) && !arr2@.contains(
                #[trigger] result[i],
            )),
        forall|i: int|
            0 <= i < arr1.len() ==> (arr2@.contains(#[trigger] arr1[i]) || result@.contains(
                #[trigger] arr1[i],
            )),
{
    let mut output_str = Vec::new();
    let mut index: usize = 0;

    while index < arr1.len()
        invariant
            index <= arr1.len(),
            output_str.len() == index,
            arr1.len() == old(arr1).len(),
            arr2.len() == old(arr2).len(),
            forall |i: int| 0 <= i < index ==> (output_str[i] == arr1[i] && !arr2@.contains(output_str[i])),
    {
        if (!contains(arr2, arr1[index])) {
            output_str.push(arr1[index]);
        }
        index += 1;
    }
    output_str
}

} // verus!

// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1