
use vstd::prelude::*;

fn main() {}

verus! {

fn contains(str: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
{
    let mut i = 0;
    while (i < str.len())
        invariant
            forall |j: int| 0 <= j < i ==> str[j] != key,
            i <= str.len(),
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

    while (index < arr1.len())
        invariant
            index <= arr1.len(),
            output_str.len() == index,
            forall |j: int| 0 <= j < index ==> arr2@.contains(output_str[j]),
        {
        if (!contains(arr2, arr1[index])) {
            output_str.push(arr1[index]);
        }
        index += 1;
    }
    output_str
}

} // verus!

// is safe: False
// Score: Compilation Error: False, Verified: 2, Errors: 2, Verus Errors: 4