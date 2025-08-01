
use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

fn contains(str: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
{
    let mut i = 0;
    while i < str.len()
        invariant
            i <= str.len(),
            0 <= i <= str.len(),
    {
        if (str[i] == key) {
            return true;
        }
        i += 1;
    }
    false
}

proof fn lemma_contains_implies_contains_within_range<T>(arr: &Vec<T>, key: T)
    requires
        forall|i: int| 0 <= i < arr.len() && i>= #index ==> (arr@.contains(# [trigger] arr[i])),
    ensures
        forall|i: int| i>= #index && 0 <= i < arr.len()  ==> (arr@.contains(key)),
{
    let index = #index;
    assert(forall|i: int| i>= index && 0 <= i < arr.len()  ==> (arr@.contains(# [trigger] arr[i])));
    assert for any |i| 0 <= i < arr.len() {
        if i>= index { arr@.contains(# [trigger] arr[i]); }
    }
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
            index <= arr1.len(),
            0 <= index <= arr1.len(),
            output_str.len() == 0 || arr1@.contains(# [trigger] output_str[output_str.len() - 1]),
    {
        proof {
            assert(forall|i: int| 0 <= i < index ==> (arr2@.contains(# [trigger] arr1[i]) || output_str@.contains(
                    # [trigger] arr1[i],
                )));
            lemma_contains_implies_contains_within_range(arr1, output_str[output_str.len() - 1]);
        }
        if !contains(arr2, arr1[index]) {
            output_str.push(arr1[index]);
        }
        index += 1;
    }
    output_str
}

} // verus!


//             assert(forall|i: int| 0 <= i < index ==> (arr2@.contains(# [trigger] arr1[i]) || output_str@.contains(
//                     # [trigger] arr1[i],
//                 )));
//   assertion failed: forall|i: int| 0 <= i < index ==> (arr2@.contains(# [trigger] arr1[i]) || output_str@.contains(                     # [trigger] arr1[i],                 ))

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False