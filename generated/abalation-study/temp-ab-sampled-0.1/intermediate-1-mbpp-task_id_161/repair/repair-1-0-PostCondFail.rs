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
        invariant 0 <= i <= str.len(),
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
        invariant 0 <= index <= arr1.len(),
    {
        if (!contains(arr2, arr1[index])) {
            output_str.push(arr1[index]);
        }
        index += 1;
    }
    proof {
        assert(forall|i: int| 0 <= i < arr1.len() ==> (arr2@.contains(arr1[i]) || output_str@.contains(arr1[i]))); // Added by AI
    }
    output_str
}

} // verus!

// failed this postcondition
//         forall|i: int|
//             0 <= i < arr1.len() ==> (arr2@.contains(#[trigger] arr1[i]) || result@.contains(
//                 #[trigger] arr1[i],
//             )),
// at the end of the function body
// {
//     let mut output_str = Vec::new();
//     let mut index: usize = 0;
// 
// ...
//     output_str
// }
//   at the end of the function body: {     let mut output_str = Vec::new();     let mut index: usize = 0;      while index < arr1.len()          invariant 0 <= index <= arr1.len(),     {         if (!contains(arr2, arr1[index])) {             output_str.push(arr1[index]);         }         index += 1;     }     output_str }
//   failed this postcondition: forall|i: int|             0 <= i < arr1.len() ==> (arr2@.contains(#[trigger] arr1[i]) || result@.contains(                 #[trigger] arr1[i],             ))

// Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 3
// Safe: True