
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

proof fn lemma_sum_to_bound(arr: Seq<i64>, index: int)
    requires
        index >= 0 && index <= arr.len(),
        forall |i: int| 0 <= i && i < arr.len() ==> arr[i] >= i64::MIN && arr[i] <= i64::MAX,
    ensures
        sum_to(arr.subrange(0, index)) >= i128::MIN && sum_to(arr.subrange(0, index)) <= i128::MAX,
{
    if index == 0 {
        assert(sum_to(arr.subrange(0, 0)) == 0);
    } else {
        lemma_sum_to_bound(arr, index - 1);
        assert(sum_to(arr.subrange(0, index)) == sum_to(arr.subrange(0, index - 1)) + arr[(index - 1) as int]);
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
        assert(sum + arr[( index ) as int] as i128 >= i128::MIN && sum + arr[( index ) as int] as i128 <= i128::MAX) by {
            lemma_sum_to_bound(arr@, index as int + 1);
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