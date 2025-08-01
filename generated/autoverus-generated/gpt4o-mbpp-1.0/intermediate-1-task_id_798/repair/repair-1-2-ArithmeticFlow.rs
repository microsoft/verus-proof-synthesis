
#[allow(unused_imports)]
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
proof fn lemma_monotonic_append(arr: Seq<i64>, elem: i64)
    ensures
        sum_to(arr.push(elem)) == sum_to(arr) + elem,
{
    if arr.len() == 0 {
        assert(sum_to(arr.push(elem)) == elem);
        assert(sum_to(arr) + elem == elem);
    } else {
        lemma_monotonic_append(arr.drop_last(), arr.last());
        assert(sum_to(arr.push(elem)) == sum_to(arr.drop_last().push(arr.last())) + elem);
        assert(sum_to(arr.drop_last().push(arr.last())) == sum_to(arr));
        assert(sum_to(arr.push(elem)) == sum_to(arr) + elem);
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
            arr.len() == arr.len(),
            index <= arr.len(),
            sum == sum_to(arr@.subrange(0, index as int)) as i128,
            index < arr.len(),
            arr.len() == arr.len(),
    {
        // Assertion to prevent arithmetic overflow and underflow
        assert(sum + arr[( index ) as int] as i128 <= i128::MAX && sum + arr[( index ) as int] as i128 >= i128::MIN) by {
            lemma_monotonic_append(arr@.subrange(0, index as int), arr[( index ) as int]);
            reveal(sum_to);
        };

        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!





//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False