use vstd::prelude::*;
fn main() {
    // Write a function to find the second smallest number in a list.
    // change the signatue to return -> (min_index, second_min_index)
    assert_eq!(second_smallest(&vec![1, 2, -8, -2, 0, -2]), (2, 3));
    assert_eq!(second_smallest(&vec![2, 2, 1]), (2, 0));
    assert_eq!(second_smallest(&vec![-2, -3, -2]), (1, 0));
    assert_eq!(second_smallest(&vec![-2, -2, -2]), (0, 1));
}

verus! {

spec fn min_spec(seq: Seq<i32>) -> int
    recommends
        0 < seq.len(),
    decreases seq.len(),
{
    if seq.len() == 1 {
        seq[0] as int
    } else if seq.len() == 0 {
        0
    } else {
        let later_min = min_spec(seq.drop_first());
        if seq[0] <= later_min {
            seq[0] as int
        } else {
            later_min as int
        }
    }
}

// change the signatue to return -> (min_index, second_min_index)
fn second_smallest(numbers: &Vec<i32>) -> (indices: (
    usize,
    usize,
))  //(min_index, second_min_index)
    requires
        numbers.len()
            >= 2,  // There must be at least 2 different values, a minimum and another one

    ensures
        forall|k: int|
            0 <= k < numbers.len() && k != indices.0 && numbers[indices.0 as int] == min_spec(
                numbers@,
            ) ==> (#[trigger] numbers[k] >= numbers[indices.1 as int]),
        exists|k: int|
            0 <= k < numbers.len() && k != indices.0 && (#[trigger] numbers[k]
                == numbers[indices.1 as int]),
{
    let mut min_index: usize = 0;
    let mut second_min_index: usize = 1;

    if numbers[1] < numbers[0] {
        min_index = 1;
        second_min_index = 0;
    }
    let mut index = 2;
    while index < numbers.len()
        invariant
            0 <= index <= numbers.len(),
            0 <= min_index < index,
            0 <= second_min_index < index,
            min_index != second_min_index,
            forall|k: int| 0 <= k < index ==> numbers[k] >= numbers[min_index as int],
            forall|k: int|
                0 <= k < index && k != min_index ==> numbers[k] >= numbers[second_min_index as int],
    {
        if numbers[index] < numbers[min_index] {
            second_min_index = min_index;
            min_index = index;
        } else if numbers[index] < numbers[second_min_index] {
            second_min_index = index;
        }
        index += 1;
        assert(forall|k: int|
            0 <= k < index && k != min_index ==> numbers[k] >= numbers[second_min_index as int]);
    }
    assert(forall|k: int|
        0 <= k < index && k != min_index ==> numbers[k] >= numbers[second_min_index as int]);
    assert(forall|k: int|
        0 <= k < numbers.len() && k != min_index && numbers[min_index as int] == min_spec(numbers@)
            ==> (numbers[k] >= numbers[second_min_index as int]));
    (min_index, second_min_index)
}

} // verus!
