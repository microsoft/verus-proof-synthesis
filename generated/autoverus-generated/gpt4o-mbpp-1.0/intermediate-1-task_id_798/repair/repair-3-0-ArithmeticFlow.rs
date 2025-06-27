
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_isolation(false)]

    spec fn sum_to(arr: Seq<i64>) -> int
        decreases arr.len(),
    {
        if arr.len() == 0 {
            0
        } else {
            sum_to(arr.drop_last()) + arr.last()
        }
    }

    proof fn lemma_sum_to_bound(arr: Seq<i64>, idx: int)
        requires
            0 <= idx < arr.len(),
        ensures
            sum_to(arr.subrange(0, idx + 1)) >= arr[idx],
    {
        if idx == 0 {
            assert(arr[idx] <= sum_to(arr.subrange(0, idx + 1))) by {
                assert(sum_to(arr.subrange(0, idx + 1)) == arr[0]);
            };
        } else {
            lemma_sum_to_bound(arr, idx - 1);
            assert(sum_to(arr.subrange(0, idx + 1)) >= arr[idx]) by {
                assert(sum_to(arr.subrange(0, idx + 1)) == sum_to(arr.subrange(0, idx)) + arr[idx]);
                assert(sum_to(arr.subrange(0, idx + 1)) >= arr[idx]) by {
                    assert(sum_to(arr.subrange(0, idx)) >= 0); // Assuming no negative overflow
                };
            };
        }
    }

    fn sum(arr: &Vec<i64>) -> (sum: i128)
        ensures
            sum_to(arr@) == sum,
    {
        let mut index = 0;
        let mut sum = 0i128;
        while index < arr.len()
            invariant
                sum == sum_to(arr@.subrange(0, index as int)) as i128,
                index <= arr.len(),
        {
            assert(sum + arr[( index ) as int] as i128 <= sum_to(arr@));
            sum = sum + arr[index] as i128;
            index += 1;
        }
        sum
    }
} // verus!



//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: True