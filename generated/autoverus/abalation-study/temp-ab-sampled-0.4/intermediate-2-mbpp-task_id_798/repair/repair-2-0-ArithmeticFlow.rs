
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

proof fn lemma_sum_to_bound(arr: Seq<i64>)
    ensures
        sum_to(arr) <= arr.len() as int * 9223372036854775807,
{
    if arr.len() == 0 {
        // Base case: sum_to(arr) == 0
    } else {
        lemma_sum_to_bound(arr.drop_last());
        assert(sum_to(arr) == sum_to(arr.drop_last()) + arr.last());
        assert(sum_to(arr.drop_last()) <= (arr.len() - 1) as int * 9223372036854775807);
        assert(arr.last() <= 9223372036854775807);
        assert(sum_to(arr) <= arr.len() as int * 9223372036854775807);
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
            arr.len() <= 1000,
            index <= arr.len(),
            sum_to(arr@.subrange(0, index as int)) == sum as int,
            arr.len() <= 1000,
            arr.len() == arr.len(),
    {
        assert(sum + arr[( index ) as int] as i128 <= 1000 * 9223372036854775807) by {
            lemma_sum_to_bound(arr@.subrange(0, index as int + 1));
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
// Safe: True