use vstd::prelude::*;

fn main() {
    //Write a function in Rust to find the shared elements from the given two lists.

    assert_eq!(
        shared_elements(&vec![3, 4, 5, 6], &vec![5, 7, 4, 10]),
        [4, 5]
    );
    assert_eq!(
        shared_elements(&vec![1, 2, 3, 4], &vec![5, 4, 3, 7]),
        [3, 4]
    );
    assert_eq!(
        shared_elements(&vec![11, 12, 14, 13], &vec![17, 15, 14, 13]),
        [14, 13]
    );
}

verus! {

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    let mut i = 0;
    while i < arr.len()
        invariant
            forall|m: int| 0 <= m < i ==> (arr[m] != key),
    {
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
    let ghost mut shared_arr_len: int = 0;

    let mut index = 0;
    while index < list1.len()
        invariant
            forall|i: int|
                0 <= i < shared.len() ==> (list1@.contains(#[trigger] shared[i]) && list2@.contains(
                    #[trigger] shared[i],
                )),
            forall|m: int, n: int| 0 <= m < n < shared.len() ==> shared[m] != shared[n],
    {
        if (contains(list2, list1[index]) && !contains(&shared, list1[index])) {
            shared.push(list1[index]);
            proof {
                shared_arr_len = shared_arr_len + 1;
            }
        }
        index += 1
    }
    shared
}

} // verus!
