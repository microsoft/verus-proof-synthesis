use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

fn contains(str: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
{
    let mut i = 0;
    proof {
        assert(! (exists|j: int| 0 <= j < i ==> (str[j] == key))); // Added by AI
    }
    while i < str.len()
        invariant
            0 <= i <= str.len(),
            exists|j: int| 0 <= j < i ==> (str[j] == key),
            str.len() == str.len(),
    {
        if (str[i] == key) {
            return true;
        }
        i += 1;
        proof {
            assert(! (exists|j: int| 0 <= j < i ==> (str[j] == key))); // Added by AI
        }
    }
    false
}

fn remove_elements(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        forall|i: int|
            0 <= i < result.len() ==> (arr1@.contains(# [trigger] result[i]) && !arr2@.contains(
                # [trigger] result[i],
            )),
        forall|i: int|
            0 <= i < arr1.len() ==> (arr2@.contains(# [trigger] arr1[i]) || result@.contains(
                # [trigger] arr1[i],
            )),
{
    let mut output_str = Vec::new();
    let mut index: usize = 0;
    while index < arr1.len()
        invariant
            forall|j: int|
                0 <= j < output_str.len() ==> (arr1@.contains(# [trigger] output_str[j])
                    && !arr2@.contains(# [trigger] output_str[j])),
            index <= arr1.len(),
            output_str.len() <= arr1.len(),
            arr1.len() == arr1.len(),
            arr2.len() == arr2.len(),
            output_str.len() == output_str.len(),
    {
        if (!contains(arr2, arr1[index])) {
            output_str.push(arr1[index]);
        }
        index += 1;
    }
    output_str
}

} // verus!

//             exists|j: int| 0 <= j < i ==> (str[j] == key),
//   None: exists|j: int| 0 <= j < i ==> (str[j] == key)

// Compilation Error: False, Verified: 0, Errors: 3, Verus Errors: 4
// Safe: True