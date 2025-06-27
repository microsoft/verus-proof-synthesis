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

proof fn lemma_monotonic(arr: Seq<i64>, i: nat, j: nat)
    requires
        i <= j,
        j <= arr.len(),
    ensures
        sum_to(arr.subrange(0, i as int)) <= sum_to(arr.subrange(0, j as int)),
    decreases j - i
{
    if i < j {
        lemma_monotonic(arr, i, ( j - 1 ) as nat);
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
            sum_to(arr@.subrange(0, index as int)) == sum as int,
            arr.len() == arr.len(),
            // The array `arr` is never modified in this loop
            forall |k: int| 0 <= k < arr.len() ==> arr[k] == arr[k],
            sum + arr[index as int] as i128 <= i128::MAX, // Added by AI, for assertion fail
            sum + arr[index as int] as i128 >= i128::MIN, // Added by AI, for assertion fail
    {
        assert(sum + arr[( index ) as int] as i128 <= i128::MAX && sum + arr[( index ) as int] as i128 >= i128::MIN) by {
            lemma_monotonic(arr@, 0, index as nat);
        };

        sum = sum + arr[index] as i128;
        index += 1;
        proof {
            assert(sum + arr[index as int] as i128 >= i128::MIN); // Added by AI
        }
    }
    sum
}

} // verus!

//             sum + arr[index as int] as i128 >= i128::MIN, // Added by AI, for assertion fail
//   None: sum + arr[index as int] as i128 >= i128::MIN

// Compilation Error: False, Verified: 1, Errors: 3, Verus Errors: 5
// Safe: True