use vstd::prelude::*;
fn main() {}
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

fn second_smallest(numbers: &Vec<i32>) -> (indices: (usize, usize))
    requires
        numbers.len() >= 2,
    ensures
        forall|k: int|
            0 <= k < numbers.len() && k != indices.0 && numbers[indices.0 as int] == min_spec(
                numbers@,
            ) ==> (# [trigger] numbers[k] >= numbers[indices.1 as int]),
        exists|k: int|
            0 <= k < numbers.len() && k != indices.0 && (# [trigger] numbers[k]
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
            2 <= numbers.len(),
            exists|k|
                0 <= k < index && k != min_index ==> numbers[k] == numbers[(
                second_min_index) as int],
            forall|i: int|
                0 <= i < index ==> if i != min_index && i != second_min_index {
                    numbers[(second_min_index) as int] <= numbers[i]
                } else {
                    true
                },
            forall|i| 0 <= i < index ==> numbers[i] >= numbers[(min_index) as int],
            forall|j|
                0 <= j < index && j != min_index ==> numbers[j] >= numbers[(
                second_min_index) as int],
            index <= numbers.len(),
            2 <= index <= numbers.len(),
            forall|k: int|
                0 <= k < index ==> (k == min_index || k == second_min_index || numbers[k]
                    > numbers[(second_min_index) as int] || numbers[k] >= numbers[(
                min_index) as int]),
            forall|k: int|
                0 <= k < index ==> numbers[k] >= numbers[(min_index) as int] || numbers[k]
                    >= numbers[(second_min_index) as int],
            min_index < numbers.len(),
            numbers[(min_index) as int] == min_spec(numbers@.subrange(0, index as int)),
            second_min_index < numbers.len(),
    {
        if numbers[index] < numbers[min_index] {
            second_min_index = min_index;
            min_index = index;
        } else if numbers[index] < numbers[second_min_index] {
            second_min_index = index;
        }
        index += 1;
    }
    (min_index, second_min_index)
}

} // verus!


// Score: Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 3