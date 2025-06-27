
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

proof fn lemma_sum_to_monotonic(i: int, j: int)
    requires
        i <= j,
        i >= 0,
        j >= 0,
    ensures
        sum_to( Seq::new( Vec::new().len() as int ).take(j) ) >= sum_to( Seq::new( Vec::new().len() as int ).take(i) ),
{
    if i < j {
        lemma_sum_to_monotonic(i, j - 1);
    }
}

fn sum(arr: &Vec<i64>) -> (sum: i128)
    ensures
        sum == sum_to(arr@) as i128,
{
    let mut index = 0;
    let mut sum = 0i128;
    while index < arr.len()
        invariant
            index <= arr.len(),
            sum == sum_to(arr@.take(index as int)) as i128,
            index >= 0,
            arr.len() >= 0,
    {
        const current_element = arr[index] as i128;

        // Ensure that adding current_element won't cause overflow or underflow
        assert(sum + current_element <= i128::MAX) by {
            // Use the lemma to prove that the sum increases monotonically
            lemma_sum_to_monotonic(index as int, arr.len() as int);
        };

        sum = sum + current_element;
        index += 1;
    }
    sum
}

}


//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False