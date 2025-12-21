use vstd::prelude::*;

fn main() {
    // Write a function in Rust to find the sum of numbers in a list within a range specified by two indices.

    assert_eq!(
        sum_range_list(&vec![2, 1, 5, 6, 8, 3, 4, 9, 10, 11, 8, 12], 8, 10),
        29
    );
    assert_eq!(
        sum_range_list(&vec![2, 1, 5, 6, 8, 3, 4, 9, 10, 11, 8, 12], 5, 7),
        16
    );
    assert_eq!(
        sum_range_list(&vec![2, 1, 5, 6, 8, 3, 4, 9, 10, 11, 8, 12], 7, 10),
        38
    );
}

verus! {

spec fn sum_to(arr: Seq<i64>) -> int
    decreases arr.len(),
{
    if arr.len() == 0 {
        0
    } else {
        sum_to(arr.drop_last()) + arr.last()
    }
}

fn sum_range_list(arr: &Vec<i64>, start: usize, end: usize) -> (sum: i128)
    requires
        0 <= start <= end,
        start <= end < arr.len(),
    ensures
        sum_to(arr@.subrange(start as int, end + 1 as int)) == sum,
{
    let mut index = start;
    let mut sum = 0i128;
    let _end = end + 1;

    while index < _end
        invariant
            start <= _end <= arr.len(),
            start <= index <= _end,
            sum == sum_to(arr@.subrange(start as int, index as int)),
            forall|j: int|
                start <= j <= index ==> (i64::MIN * index <= (sum_to(
                    #[trigger] arr@.subrange(start as int, j),
                )) <= i64::MAX * index),
    {
        assert(arr@.subrange(start as int, index as int) =~= arr@.subrange(
            start as int,
            (index + 1) as int,
        ).drop_last());
        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!
