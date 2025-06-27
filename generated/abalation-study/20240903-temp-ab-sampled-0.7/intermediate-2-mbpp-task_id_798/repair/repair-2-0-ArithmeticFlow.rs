
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

proof fn lemma_sum_to_bounded(arr: Seq<i64>, bound: int)
    requires
        forall |i: int| 0 <= i < arr.len() ==> arr[i] <= bound,
        arr.len() > 0,
    ensures
        sum_to(arr) <= arr.len() as int * bound,
{
    if arr.len() == 1 {
        assert(sum_to(arr) == arr[0]);
    } else {
        lemma_sum_to_bounded(arr.drop_last(), bound);
        assert(sum_to(arr) <= (arr.len() - 1) as int * bound + arr.last());
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
            arr.len() == arr@.len(),
            index <= arr.len(),
            sum == sum_to(arr@.subrange(0, index as int)) as i128,
            arr.len() == arr.len(),
            forall |k: int| 0 <= k < arr.len() ==> arr[k] == arr@[k], // arr is not modified in the loop
    {
        // Assuming a reasonable bound for elements in arr
        let bound: i128 = 10000; // Example bound

        assert(arr[( index ) as int] as i128 >= -bound && arr[( index ) as int] as i128 <= bound);
        assert(sum + arr[( index ) as int] as i128 <= sum_to(arr@) as i128) by {
            lemma_sum_to_bounded(arr@, ( bound ) as int);
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