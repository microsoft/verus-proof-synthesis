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

proof fn lemma_sum_to_monotonic(arr: Seq<i64>, i: int, j: int)
    requires
        0 <= i <= j <= arr.len(),
    ensures
        sum_to(arr.subrange(0, i)) <= sum_to(arr.subrange(0, j)),
    decreases j
{
    if i < j {
        lemma_sum_to_monotonic(arr, i, j - 1);
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
            // Remove the problematic index < arr.len() invariant
    {
        assert(index < arr.len()); // Added by AI
        assert(sum + arr[(index) as int] as i128 <= (i128::MAX as i64) as i128) by {
            lemma_sum_to_monotonic(arr@, 0, index as int);
        };
        assert(sum + arr[(index) as int] as i128 >= (i128::MIN as i64) as i128) by {
            lemma_sum_to_monotonic(arr@, 0, index as int);
        };

        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!

//             index < arr.len(),
//   None: index < arr.len()

// Compilation Error: False, Verified: 1, Errors: 3, Verus Errors: 5
// Safe: True