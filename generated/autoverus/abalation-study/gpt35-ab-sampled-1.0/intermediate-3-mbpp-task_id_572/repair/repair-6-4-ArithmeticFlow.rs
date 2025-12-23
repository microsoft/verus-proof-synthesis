
use vstd::prelude::*;
fn main() {}

verus! {
    // ... (specification functions and other code)

    proof fn lemma_monotonic_index_count_frequency_rcr(index: int, arr: Seq<i32>, key: i32)
        requires
            0 <= index <= arr.len(),
            index < arr.len(),
            count_frequency_rcr(arr@.subrange(0, index as int), key) <= count_frequency_rcr(arr@, key),
        ensures
            count_frequency_rcr(arr@.subrange(0, (index + 1) as int), key) <= count_frequency_rcr(arr@, key),
        decreases index
    {
        // Prove the monotonicity of count_frequency_rcr using loop invariance or induction
        // ...
    }

    // ... (other proof functions)

    fn count_frequency(arr: &Vec<i32>, key: i32) -> (frequency: usize)
        ensures
            count_frequency_rcr(arr@, key) == frequency,
    {
        let mut index = 0;
        let mut counter = 0;
        while index < arr.len()
            invariant
                count_frequency_rcr(arr@.subrange(0, index as int), key) == counter,
                index <= arr.len(),
        {
            if (arr[index] == key) {
                assert(counter + 1 <= count_frequency_rcr(arr@, key)) by {
                    lemma_monotonic_index_count_frequency_rcr(index as int, arr@, key);
                }
                counter += 1;
            }
            index += 1;
        }
        counter
    }

    // ... (other functions and specifications)
}


//             counter += 1;
//   None: counter += 1

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 7
// Safe: False