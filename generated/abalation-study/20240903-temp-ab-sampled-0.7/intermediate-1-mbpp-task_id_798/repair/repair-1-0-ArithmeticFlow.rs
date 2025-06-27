
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

// Lemma function to show the monotonicity of sum_to
proof fn lemma_sum_to_monotonic(arr: Seq<i64>, len: nat)
    requires
        len <= arr.len(),
    ensures
        sum_to(arr.subrange(0, ( len ) as int)) <= sum_to(arr),
    decreases arr.len() - len
{
    if len < arr.len() {
        lemma_sum_to_monotonic(arr.drop_last(), len);
        assert(sum_to(arr.subrange(0, ( len ) as int)) <= sum_to(arr.drop_last()) + arr.last());
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
            sum == sum_to(arr@.subrange(0, index as int)) as i128,
            index < arr.len(),
            arr.len() == arr.len(),
    {
        // Assertion to ensure no overflow/underflow
        assert(sum + arr[( index ) as int] as i128 <= sum_to(arr@) as i128) by {
            lemma_sum_to_monotonic(arr@, index as nat + 1);
        };

        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!





//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: False, Verified: 1, Errors: 3, Verus Errors: 7
// Safe: True