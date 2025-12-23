
use vstd::prelude::*;
fn main() {}

verus! {

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
        sum_to(arr.subrange(0, ( i ) as int)) <= sum_to(arr.subrange(0, ( j ) as int)),
    decreases j
{
    if i < j {
        lemma_monotonic(arr, i, (j-1) as nat);
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
        assert(index < arr.len());
        assert(sum + arr[( index ) as int] as i128 <= sum_to(arr@) as i128) by{
            lemma_monotonic(arr@, index as nat, arr.len() as nat);
        };

        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!





//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: False, Verified: 1, Errors: 3, Verus Errors: 6
// Safe: True