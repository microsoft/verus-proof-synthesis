use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    let mut i = 0;
    while i < arr.len() {
        if (arr[i] == key) {
            return true;
        }
        i += 1;
    }
    false
}

fn shared_elements(list1: &Vec<i32>, list2: &Vec<i32>) -> (shared: Vec<i32>)
    ensures
        forall|i: int|
            0 <= i < shared.len() ==> (list1@.contains(#[trigger] shared[i]) && list2@.contains(
                #[trigger] shared[i],
            )),
        forall|i: int, j: int| 0 <= i < j < shared.len() ==> shared[i] != shared[j],
{
    let mut shared = Vec::new();
    let mut index = 0;
    while index < list1.len()
        invariant
            forall|i: int|
                0 <= i < shared.len() ==> (list1@.contains(#[trigger] shared[i]) && list2@.contains(
                    #[trigger] shared[i],
                )),
            forall|i: int, j: int| 0 <= i < j < shared.len() ==> shared[i] != shared[j],
    {
        if (contains(list2, list1[index]) && !contains(&shared, list1[index])) {
            shared.push(list1[index]);
        }
        index += 1
    }
    shared
}

} // verus!

// failed this postcondition
//         forall|i: int|
//             0 <= i < shared.len() ==> (list1@.contains(#[trigger] shared[i]) && list2@.contains(
//                 #[trigger] shared[i],
//             )),
// at the end of the function body
// {
//     let mut shared = Vec::new();
//     let mut index = 0;
//     while index < list1.len() {
// ...
//     shared
// }
//   at the end of the function body: {     let mut shared = Vec::new();     let mut index = 0;     while index < list1.len() {         if (contains(list2, list1[index]) && !contains(&shared, list1[index])) {             shared.push(list1[index]);         }         index += 1     }     shared }
//   failed this postcondition: forall|i: int|             0 <= i < shared.len() ==> (list1@.contains(#[trigger] shared[i]) && list2@.contains(                 #[trigger] shared[i],             ))

// Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 1
// Safe: True