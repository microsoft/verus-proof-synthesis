use vstd::prelude::*;

fn main() {}

verus! {
proof fn lemma_vec_remove<T>(vec: Seq<T>, i: int)
    requires
        0 <= i < vec.len(),
    ensures
        forall |k: int| 0 <= k < i ==> #[trigger] vec[k] == vec.remove(i)[k],
        forall |k: int| i < k  < vec.len() ==> #[trigger] vec[k] ==  vec.remove(i)[k-1],
{
    
}

proof fn lemma_vec_push<T>(vec: Seq<T>, i: T, l: usize)
    requires
        l == vec.len(),
    ensures
        forall |k: int| 0 <= k < vec.len() ==> #[trigger] vec[k] == vec.push(i)[k],
        vec.push(i).index(l as int) == i,
{
}

#[verifier::loop_isolation(false)]

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    let mut index = 0;
    while index < arr.len()
        invariant
            forall |j: int| 0 <= j < index ==> arr[j] != key,
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
            0 <= i < arr1.len() ==> (!arr2@.contains(#[trigger] arr1[i]) ==> result@.contains(
                arr1[i],
            )),
        forall|i: int|
            0 <= i < arr2.len() ==> (!arr1@.contains(#[trigger] arr2[i]) ==> result@.contains(
                arr2[i],
            )),
        forall|i: int, j: int|
            0 <= i < j < result.len() ==> #[trigger] result[i] != #[trigger] result[j],
{
    let mut result = Vec::new();
    let mut index = 0;
    while index < arr1.len()
        invariant
            index <= arr1.len(),
            forall |i: int, j: int| 0 <= i < j < result.len() ==> #[trigger] result[i] != #[trigger] result[j],
    {
        if (!contains(arr2, arr1[index]) && !contains(&result, arr1[index])) {
            proof { lemma_vec_push(result@, arr1[( index ) as int], result.len()); }
            result.push(arr1[index]);
        }
        index += 1;
    }
    
    let ghost old_result = result@;
    index = 0;
    while index < arr2.len()
        invariant
            index <= arr2.len(),
            forall |i:int| 0 <= i < index ==>
                (!arr1@.contains(arr2[i]) ==> (result@.contains(arr2[i]) || old_result.contains(arr2[i]))),
            forall |i: int, j: int| 0 <= i < j < result.len() ==> #[trigger] result[i] != #[trigger] result[j],
    {
        if (!contains(arr1, arr2[index]) && !contains(&result, arr2[index])) {
            proof { lemma_vec_push(result@, arr2[( index ) as int], result.len()); }
            result.push(arr2[index]);
        }
        index += 1;
    }
    result
}

}

// failed this postcondition
//         forall|i: int, j: int|
//             0 <= i < j < result.len() ==> #[trigger] result[i] != #[trigger] result[j],
// at the end of the function body
// {
//     let mut result = Vec::new();
//     let mut index = 0;
//     while index < arr1.len()
// ...
//     result
// }
//   at the end of the function body: {     let mut result = Vec::new();     let mut index = 0;     while index < arr1.len()         invariant             index <= arr1.len(),     {         if (!contains(arr2, arr1[index]) && !contains(&result, arr1[index])) {             proof { lemma_vec_push(result@, arr1[( index ) as int], result.len()); }             result.push(arr1[index]);         }         index += 1;     }          let ghost old_result = result@;     index = 0;     while index < arr2.len()         invariant             index <= arr2.len(),             forall |i:int| 0 <= i < index ==>                 (!arr1@.contains(arr2[i]) ==> (result@.contains(arr2[i]) || old_result.contains(arr2[i]))),     {         if (!contains(arr1, arr2[index]) && !contains(&result, arr2[index])) {             proof { lemma_vec_push(result@, arr2[( index ) as int], result.len()); }             result.push(arr2[index]);         }         index += 1;     }     result }
//   failed this postcondition: forall|i: int, j: int|             0 <= i < j < result.len() ==> #[trigger] result[i] != #[trigger] result[j]

// Compilation Error: False, Verified: 5, Errors: 1, Verus Errors: 2
// Safe: True