use vstd::prelude::*;

fn main() {
    // Write a function in Rust that takes in a list and an element and inserts the element before each element in the list, and returns the resulting list.

    // ***chagne the MBPP test input from string to integer
    assert_eq!(
        insert_before_each(&vec![10, 4, 6, 9], 1),
        [1, 10, 1, 4, 1, 6, 1, 9]
    );
    assert_eq!(
        insert_before_each(&vec![1, 1, 1, 1], 0),
        [0, 1, 0, 1, 0, 1, 0, 1]
    );
    assert_eq!(
        insert_before_each(&vec![-3, -2, -1, 1, 2, 3], 0),
        [0, -3, 0, -2, 0, -1, 0, 1, 0, 2, 0, 3]
    );
}

verus! {

fn insert_before_each(arr: &Vec<i32>, elem: i32) -> (result: Vec<i32>)
    ensures
        result@.len() == (2 * arr.len()),
        forall|k: int| 0 <= k < arr.len() ==> #[trigger] result[2 * k] == elem,
        forall|k: int| 0 <= k < arr.len() ==> #[trigger] result[2 * k + 1] == arr[k],
{
    let mut result: Vec<i32> = Vec::new();
    let mut index = 0;

    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            result@.len() == index * 2,
            forall|k: int| 0 <= k < index ==> #[trigger] result[2 * k] == elem,
            forall|k: int| 0 <= k < index ==> #[trigger] result[2 * k + 1] == arr[k],
    {
        result.push(elem);
        result.push(arr[index]);
        index += 1;
    }
    result
}

} // verus!
