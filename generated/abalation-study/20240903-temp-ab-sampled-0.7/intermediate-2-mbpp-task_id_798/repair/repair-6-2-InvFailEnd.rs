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
        sum_to(arr.subrange(0, index as int)) <= sum_to(arr.subrange(0, (index + 1) as int)),
{
    // Prove monotonicity of sum_to
    assert(sum_to(arr.subrange(0, (index + 1) as int)) == sum_to(arr.subrange(0, index as int)) + arr[( index ) as int]);
    assert(sum_to(arr.subrange(0, index as int)) <= sum_to(arr.subrange(0, index as int)) + arr[( index ) as int]);
}

fn sum(arr: &Vec<i64>) -> (sum: i128)
    ensures
        sum_to(arr@) == sum,
{
    let mut index = 0;
    let mut sum = 0i128;
    while index < arr.len()
        invariant
            arr.len() == arr@.len(),
            index <= arr.len(),
            sum == sum_to(arr@.subrange(0, index as int)) as i128,
            arr.len() == arr.len(),
            forall |k: int| 0 <= k < arr.len() ==> arr[k] == arr@[k], // arr is not modified in the loop
            forall |j: int| 0 <= j < index ==> (sum as i128).checked_add(arr[j as int] as i128).is_some(), // Added by AI, for assertion fail
            (sum as i128).checked_add(arr[(index) as int] as i128).is_some(), // Ensure no overflow in next iteration
    {
        // Assertion to prevent overflow
        assert((sum as i128).checked_add(arr[( index ) as int] as i128).is_some());

        sum = sum + arr[index] as i128;
        index += 1;

        proof {
            assert(forall |j: int| 0 <= j < index ==> (sum as i128).checked_add(arr[j as int] as i128).is_some());
        } // Added by AI
    }
    sum
}

}

//             (sum as i128).checked_add(arr[(index) as int] as i128).is_some(), // Ensure no overflow in next iteration
//   None: (sum as i128).checked_add(arr[(index) as int] as i128).is_some()

// Compilation Error: False, Verified: 1, Errors: 3, Verus Errors: 6
// Safe: True