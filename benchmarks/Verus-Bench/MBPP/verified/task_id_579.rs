use vstd::prelude::*;

fn main() {
    // Write a function in Rust to get the difference between two lists.

    assert_eq!(
        find_dissimilar(&vec![3, 4, 5, 6], &vec![5, 7, 4, 10]),
        [3, 6, 7, 10]
    );
    assert_eq!(
        find_dissimilar(&vec![1, 2, 3, 4], &vec![7, 2, 3, 9]),
        [1, 4, 7, 9]
    );
    assert_eq!(
        find_dissimilar(&vec![21, 11, 25, 26], &vec![26, 34, 21, 36]),
        [11, 25, 34, 36]
    );
}

verus! {

proof fn lemma_vec_push<T>(vec: Seq<T>, i: T, l: usize)
    requires
        l == vec.len(),
    ensures
        forall|k: int| 0 <= k < vec.len() ==> #[trigger] vec[k] == vec.push(i)[k],
        vec.push(i).index(l as int) == i,
{
}

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    let mut index = 0;
    while index < arr.len()
        invariant
            forall|m: int| 0 <= m < index ==> (arr[m] != key),
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
    let ghost mut output_len: int = 0;

    let mut index = 0;
    while index < arr1.len()
        invariant
            forall|i: int|
                0 <= i < index ==> (!arr2@.contains(#[trigger] arr1[i]) ==> result@.contains(
                    arr1[i],
                )),
            forall|m: int, n: int|
                0 <= m < n < result.len() ==> #[trigger] result[m] != #[trigger] result[n],
    {
        if (!contains(arr2, arr1[index]) && !contains(&result, arr1[index])) {
            proof {
                lemma_vec_push(result@, arr1[index as int], result.len());
                output_len = output_len + 1;
            }
            result.push(arr1[index]);

        }
        index += 1;
    }
    let mut index = 0;
    while index < arr2.len()
        invariant
            forall|i: int|
                0 <= i < arr1.len() ==> (!arr2@.contains(#[trigger] arr1[i]) ==> result@.contains(
                    arr1[i],
                )),
            forall|i: int|
                0 <= i < index ==> (!arr1@.contains(#[trigger] arr2[i]) ==> result@.contains(
                    arr2[i],
                )),
            forall|m: int, n: int|
                0 <= m < n < result.len() ==> #[trigger] result[m] != #[trigger] result[n],
    {
        if (!contains(arr1, arr2[index]) && !contains(&result, arr2[index])) {
            proof {
                lemma_vec_push(result@, arr2[index as int], result.len());
                output_len = output_len + 1;
            }
            result.push(arr2[index]);
        }
        index += 1;
    }
    assert(forall|i: int|
        0 <= i < arr1.len() ==> (!arr2@.contains(#[trigger] arr1[i]) ==> result@.contains(
            arr1[i],
        )));
    assert(forall|i: int|
        0 <= i < arr2.len() ==> (!arr1@.contains(#[trigger] arr2[i]) ==> result@.contains(
            arr2[i],
        )));
    assert(forall|i: int, j: int|
        0 <= i < j < result.len() ==> #[trigger] result[i] != #[trigger] result[j]);

    result
}

} // verus!
