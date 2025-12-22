use vstd::prelude::*;

fn main() {
    // Write a function in Rust to remove all elements from a given list present in another list.

    assert_eq!(
        remove_elements(&vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10], &vec![2, 4, 6, 8]),
        [1, 3, 5, 7, 9, 10]
    );
    assert_eq!(
        remove_elements(&vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10], &vec![1, 3, 5, 7]),
        [2, 4, 6, 8, 9, 10]
    );
    assert_eq!(
        remove_elements(&vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10], &vec![5, 7]),
        [1, 2, 3, 4, 6, 8, 9, 10]
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

fn contains(str: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
{
    let mut i = 0;
    while i < str.len()
        invariant
            forall|m: int| 0 <= m < i ==> (str[m] != key),
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
    let ghost mut output_len: int = 0;

    while index < arr1.len()
        invariant
            forall|k: int|
                0 <= k < output_str.len() ==> (arr1@.contains(#[trigger] output_str[k])
                    && !arr2@.contains(#[trigger] output_str[k])),
            forall|k: int|
                0 <= k < index ==> (arr2@.contains(#[trigger] arr1[k]) || output_str@.contains(
                    #[trigger] arr1[k],
                )),
    {
        if (!contains(arr2, arr1[index])) {
            proof {
                lemma_vec_push(output_str@, arr1[index as int], output_str.len());
                output_len = output_len + 1;
            }
            output_str.push(arr1[index]);
        }
        index += 1;
    }
    output_str
}

} // verus!
