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
            forall|k: int| 0 <= k < numbers.len() ==> numbers[k] == numbers[k], // The array is never changed in the loop
            forall|j: int|
                0 <= j < index && j != min_index ==> if j != second_min_index {
                    numbers[j] >= numbers[(second_min_index) as int]
                } else {
                    true
                },
            forall|j: int|
                0 <= j < index ==> if j != min_index {
                    numbers[j] >= numbers[(min_index) as int]
                } else {
                    true
                },
            index <= numbers.len(),
            min_index < numbers.len(),
            numbers.len() >= 2,
            second_min_index < numbers.len(),
            numbers.len() >= 2,
            numbers.len() == numbers.len(), // Loop invariant specifying the length of the array
            if index > 1 { exists|k: int| 0 <= k < index && k != min_index && numbers[k] == numbers[second_min_index as int] } else { true }, // Added by AI, for assertion fail
    {
        if numbers[index] < numbers[min_index] {
            second_min_index = min_index;
            min_index = index;

            proof {
                assert(index >= 2); // Index is increased, so there are at least two processed elements
                assert(exists|k: int| 0 <= k < index && k != min_index && numbers[k] == numbers[second_min_index as int]);
            }

        } else if numbers[index] < numbers[second_min_index] {
            second_min_index = index;

            proof {
                assert(index >= 2); // Index is increased, so there are at least two processed elements
                assert(exists|k: int| 0 <= k < index && k != min_index && numbers[k] == numbers[second_min_index as int]);
            }
        }

        index += 1;

        proof {
            // If the if-else statements are not entered, the initial condition is preserved
            assert(index >= 2); // Index is increased, so there are at least two processed elements
            assert(if index > 1 { exists|k: int| 0 <= k < index && k != min_index && numbers[k] == numbers[second_min_index as int] } else { true });
        }
    }
    (min_index, second_min_index)
}

} // verus!

//                 assert(exists|k: int| 0 <= k < index && k != min_index && numbers[k] == numbers[second_min_index as int]);
//   assertion failed: exists|k: int| 0 <= k < index && k != min_index && numbers[k] == numbers[second_min_index as int]

// Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 5
// Safe: True