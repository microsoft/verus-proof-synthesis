
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

proof fn lemma_sum_to_monotonic(arr: Seq<i64>, i: nat)
    requires
        i <= arr.len(),
    ensures
        sum_to(arr.subrange(0, ( i ) as int)) <= sum_to(arr),
    decreases arr.len() - i
{
    if i < arr.len() {
        lemma_sum_to_monotonic(arr, i + 1);
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
        // Add assertion about the bound of `sum + arr[index] as i128`
        assert(
            sum + arr[( index ) as int] as i128 >= i128::MIN 
            && sum + arr[( index ) as int] as i128 <= i128::MAX
        ) by {
            lemma_sum_to_monotonic(arr@, index as nat);
        };

        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!





//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: False, Verified: 1, Errors: 3, Verus Errors: 5
// Safe: True