use vstd::prelude::*;

fn main() {
    //Write a function in Rust to calculate the sum of the negative numbers of a given list of numbers.

    assert_eq!(sum_negatives(&vec![2, 4, -6, -9, 11, -12, 14, -5, 17]), -32);
    assert_eq!(sum_negatives(&vec![10, 15, -14, 13, -18, 12, -20]), -52);
    assert_eq!(
        sum_negatives(&vec![19, -65, 57, 39, 152, -639, 121, 44, 90, -190]),
        -894
    );
}

verus! {

spec fn sum_negative_to(seq: Seq<i64>) -> int
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        sum_negative_to(seq.drop_last()) + if (seq.last() < 0) {
            seq.last() as int
        } else {
            0 as int
        }
    }
}

fn sum_negatives(arr: &Vec<i64>) -> (sum_neg: i128)
    ensures
        sum_negative_to(arr@) == sum_neg,
{
    let mut index = 0;
    let mut sum_neg = 0i128;

    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            forall|j: int|
                0 <= j <= index ==> (i64::MIN * index <= (sum_negative_to(
                    #[trigger] arr@.subrange(0, j),
                )) <= 0),
            sum_negative_to(arr@.subrange(0, index as int)) == sum_neg,
    {
        if (arr[index] < 0) {
            sum_neg = sum_neg + (arr[index] as i128);
        }
        index += 1;
        assert(arr@.subrange(0, index - 1 as int) == arr@.subrange(0, index as int).drop_last());

    }
    assert(arr@ == arr@.subrange(0, index as int));
    sum_neg
}

} // verus!
