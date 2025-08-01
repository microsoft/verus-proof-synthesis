
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

    proof fn lemma_monotonic_sum_to(prev: Seq<i64>, next: Seq<i64>) 
        requires prev.len() < next.len(),
        ensures sum_to(prev) <= sum_to(next),
        decreases next.len()
    {
        if prev.len() < next.len() {
            lemma_monotonic_sum_to(prev, next.drop_last());
        }
    }

    fn sum(arr: &Vec<i64>) -> (sum: i128)
        ensures sum_to(arr@) == sum,
    {
        let mut index = 0;
        let mut sum = 0i128;

        while index < arr.len()
            invariant
                0 <= index < arr.len(),
                sum <= sum_to(arr[..index].to_vec()) as i128,
                sum_to(arr[index..].to_vec()) as i128 < std::i128::MAX - arr[index] as i128,
        {
            assert!(sum + arr[index] as i128 >= sum, "Potential overflow");
            assert!(sum + arr[index] as i128 <= std::i128::MAX - arr[index] as i128, "Potential underflow");

            sum = sum + arr[index] as i128;
            index += 1;
        }
        sum
    }
}


//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False