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

proof fn lemma_sum_to_monotonic(arr: Seq<i64>, index: nat)
    requires
        index < arr.len(),
    ensures
        sum_to(arr.take(( index + 1 ) as int)) <= sum_to(arr),
    decreases arr.len() - index
{
    if index == 0 {
        // Base case: sum_to(arr.take(1)) == arr[0] <= sum_to(arr)
    } else {
        lemma_sum_to_monotonic(arr, ( index - 1 ) as nat);
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
            index <= arr.len(),
            sum <= i128::MAX, // Fixed by AI
            sum >= i128::MIN, // Fixed by AI
    {

        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!


// Score: Compilation Error: False, Verified: 1, Errors: 3, Verus Errors: 4