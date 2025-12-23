use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]
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
            (index >= 2 ==> min_index < index) && (index >= 2 ==> second_min_index < index),
            (numbers[(min_index) as int] <= numbers[(second_min_index) as int]),
            2 <= numbers.len(),
            forall|j: int|
                0 <= j < index && j != min_index ==> numbers[j] >= numbers[(
                second_min_index) as int],
            forall|j: int|
                0 <= j < index ==> numbers[j] >= numbers[(min_index) as int] || numbers[j]
                    >= numbers[(second_min_index) as int],
            forall|k: int|
                0 <= k < index ==> numbers[k] >= numbers[min_index as int] || numbers[k]
                    >= numbers[second_min_index as int],
            index <= numbers.len(),
            min_index < numbers.len(),
            numbers.len() >= 2,
            second_min_index < numbers.len(),
            numbers.len() == numbers.len(),
            index >= 2, // Added by AI
    {
        if numbers[index] < numbers[min_index] {
            second_min_index = min_index;
            min_index = index;
        } else if numbers[index] < numbers[second_min_index] {
            second_min_index = index;
        }
        index += 1;
        proof {
            assert(index >= 2);
            assert(min_index < index);
            assert(second_min_index < index);
        }
    }
    proof {
        assert(index >= 2);
        assert(min_index < index);
        assert(second_min_index < index);
        assert(exists|k: int| 0 <= k < numbers.len() && k != min_index && numbers[k] == numbers[second_min_index as int]); // Added by AI
    }
    (min_index, second_min_index)
}
}
// Score: (2, 1)
// Safe: True