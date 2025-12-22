use vstd::prelude::*;

fn main() {
    // Write a function in Rust to count number items that are identical in the same position of three given lists.

    assert_eq!(
        count_identical_position(
            &vec![1, 2, 3, 4, 5, 6, 7, 8],
            &vec![2, 2, 3, 1, 2, 6, 7, 9],
            &vec![2, 1, 3, 1, 2, 6, 7, 9]
        ),
        3
    );
    assert_eq!(
        count_identical_position(
            &vec![1, 2, 3, 4, 5, 6, 7, 8],
            &vec![2, 2, 3, 1, 2, 6, 7, 8],
            &vec![2, 1, 3, 1, 2, 6, 7, 8]
        ),
        4
    );
    assert_eq!(
        count_identical_position(
            &vec![1, 2, 3, 4, 2, 6, 7, 8],
            &vec![2, 2, 3, 1, 2, 6, 7, 8],
            &vec![2, 1, 3, 1, 2, 6, 7, 8]
        ),
        5
    );
}

verus! {

spec fn count_identical(s1: Seq<i32>, s2: Seq<i32>, s3: Seq<i32>) -> int
    decreases s1.len(), s2.len(), s3.len(),
{
    if s1.len() == 0 || s2.len() == 0 || s3.len() == 0 {
        0
    } else {
        count_identical(s1.drop_last(), s2.drop_last(), s3.drop_last()) + if (s1.last() == s2.last()
            && s2.last() == s3.last()) {
            1 as int
        } else {
            0 as int
        }
    }
}

fn count_identical_position(arr1: &Vec<i32>, arr2: &Vec<i32>, arr3: &Vec<i32>) -> (count: usize)
    requires
        arr1.len() == arr2.len() && arr2.len() == arr3.len(),
    ensures
        0 <= count <= arr1.len(),
        count_identical(arr1@, arr2@, arr3@) == count,
{
    let mut count = 0;
    let mut index = 0;
    while index < arr1.len()
        invariant
            0 <= index <= arr1.len(),
            0 <= count <= index,
            arr1.len() == arr2.len() && arr2.len() == arr3.len(),
            count_identical(
                arr1@.subrange(0, index as int),
                arr2@.subrange(0, index as int),
                arr3@.subrange(0, index as int),
            ) == count,
    {
        if arr1[index] == arr2[index] && arr2[index] == arr3[index] {
            count += 1;
        }
        index += 1;
        assert(arr1@.subrange(0, index - 1 as int) == arr1@.subrange(0, index as int).drop_last());
        assert(arr2@.subrange(0, index - 1 as int) == arr2@.subrange(0, index as int).drop_last());
        assert(arr3@.subrange(0, index - 1 as int) == arr3@.subrange(0, index as int).drop_last());
    }
    assert(arr1@ == arr1@.subrange(0, index as int));
    assert(arr2@ == arr2@.subrange(0, index as int));
    assert(arr3@ == arr3@.subrange(0, index as int));
    count
}

} // verus!
