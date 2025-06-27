use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    let mut index = 0;
    proof {
        assert(exists|i: int|
            0 <= i < arr.len() && (arr[i] == key) == (exists|j: int|
                0 <= j < index && arr[j] == key));
    }
    while index < arr.len()
        invariant
            exists|i: int|
                0 <= i < arr.len() && (arr[i] == key) == (exists|j: int|
                    0 <= j < index && arr[j] == key),
            index <= arr.len(),
            key < i32::MAX,
            key > i32::MIN,
            arr.len() == arr.len(),
            index <= i32::MAX,
            key <= arr.len() as i32, // Added by AI
    {
        if (arr[index] == key) {
            return true;
        }
        index += 1;
    }
    false
}

fn find_dissimilar(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        forall|i: int|
            0 <= i < arr1.len() ==> (!arr2@.contains(# [trigger] arr1[i]) ==> result@.contains(
                arr1[i],
            )),
        forall|i: int|
            0 <= i < arr2.len() ==> (!arr1@.contains(# [trigger] arr2[i]) ==> result@.contains(
                arr2[i],
            )),
        forall|i: int, j: int|
            0 <= i < j < result.len() ==> # [trigger] result[i] != # [trigger] result[j],
{
    let mut result = Vec::new();
    let mut index = 0;
    proof {
        assert(arr1.len() <= usize::MAX);
        assert(arr2.len() <= usize::MAX);
    }
    while index < arr1.len()
        invariant
            forall|i: int, j: int|
                0 <= i < j < result.len() ==> # [trigger] result[i] != # [trigger] result[j],
            forall|i: int|
                0 <= i < index ==> (!arr2@.contains(# [trigger] arr1[i]) && !result@.contains(
                    arr1[i],
                ) ==> result@.contains(arr1[i])),
            index <= arr1.len(),
            result.len() <= arr1.len() + arr2.len(),
            arr1.len() <= usize::MAX,
            arr2.len() <= usize::MAX,
            arr1.len() == arr1.len(),
            arr2.len() == arr2.len(),
            index <= i32::MAX,
            index <= arr1.len() as i32, // Added by AI
    {
        if (!contains(arr2, arr1[index]) && !contains(&result, arr1[index])) {
            result.push(arr1[index]);
        }
        index += 1;
    }
    let mut index = 0;
    proof {
        assert(arr1.len() <= usize::MAX);
        assert(arr2.len() <= usize::MAX);
    }
    while index < arr2.len()
        invariant
            forall|i: int, j: int|
                0 <= i < j < result.len() ==> # [trigger] result[i] != # [trigger] result[j],
            forall|i: int|
                0 <= i < arr1.len() ==> (!arr2@.contains(# [trigger] arr1[i]) && !result@.contains(
                    arr1[i],
                ) ==> result@.contains(arr1[i])),
            forall|i: int|
                0 <= i < index ==> (!arr1@.contains(# [trigger] arr2[i]) && !result@.contains(
                    arr2[i],
                ) ==> result@.contains(arr2[i])),
            index <= arr2.len(),
            result.len() <= arr1.len() + arr2.len(),
            arr1.len() <= usize::MAX,
            arr2.len() <= usize::MAX,
            arr1.len() == arr1.len(),
            arr2.len() == arr2.len(),
            index <= i32::MAX,
            index <= arr2.len() as i32, // Added by AI
    {
        if (!contains(arr1, arr2[index]) && !contains(&result, arr2[index])) {
            result.push(arr2[index]);
        }
        index += 1;
    }
    result
}

} // verus!

//             key < i32::MAX,  // Example bound
//   None: key < i32::MAX

// Compilation Error: False, Verified: 0, Errors: 4, Verus Errors: 16
// Safe: True