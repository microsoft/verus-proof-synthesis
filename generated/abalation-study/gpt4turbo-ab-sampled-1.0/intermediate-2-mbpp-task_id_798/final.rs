
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

    // Lemma to demonstrate monotonicity or bound properties could be introduced here
    proof fn sum_to_monotonic(arr: Seq<i64>, index: nat)
        requires
            arr.len() > 0, // ensures array is not empty
            index < arr.len(),
        ensures
            i128::MIN <= sum_to(arr.subrange(0, ( index + 1 ) as int)) as i128,
            sum_to(arr.subrange(0, ( index + 1 ) as int)) as i128 <= i128::MAX,
    {
        // Proof steps would go here.
    }

    fn sum(arr: &Vec<i64>) -> (sum: i128)
        ensures
            sum_to(arr@) == sum,
    {
        let mut index = 0;
        let mut sum = 0i128;
        while index < arr.len()
            invariant
                index <= arr.len(),
                sum == sum_to(arr@.subrange(0, index as int)) as i128,
                arr.len() == arr@.len(),
                i128::MIN <= sum && sum <= i128::MAX,
                forall |i: int| 0 <= i && i < index as int ==> 
                    i128::MIN <= sum + arr@[i] as i128 && sum + arr@[i] as i128 <= i128::MAX,
        {
            // Here we assert our condition prior to updating sum
            assert(i128::MIN <= sum + arr[( index ) as int] as i128 && sum + arr[( index ) as int] as i128 <= i128::MAX) by {
                sum_to_monotonic(arr@, index as nat);
            };

            sum = sum + arr[index] as i128;
            index += 1;
        }
        sum
    }
} // verus!





// Score: Compilation Error: False, Verified: 2, Errors: 2, Verus Errors: 4