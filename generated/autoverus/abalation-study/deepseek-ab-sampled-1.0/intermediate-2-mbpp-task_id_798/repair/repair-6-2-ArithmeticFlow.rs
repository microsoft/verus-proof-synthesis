
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

proof fn lemma_sum_to_monotonic(a: Seq<i64>, b: Seq<i64>)
    requires
        a.len() <= b.len(),
        b.take(a.len()) == a,
    ensures
        sum_to(a) <= sum_to(b),
{
    induction a with {
        case a == Seq::Empty {
            // Base case: a is empty
            assert(sum_to(a) == 0);
            assert(sum_to(b) >= 0); // Since b is a super-sequence, sum can't decrease
        }
        case a = Seq{ first, rest } {
            // Inductive step: assume the lemma holds for rest
            lemma_sum_to_monotonic(rest, b.drop_first());
        }
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
            0 <= index <= arr.len(),
            index <= arr.len(),
            sum == sum_to(arr@.take((index) as int)),
    {
        // Assert that adding arr[index] won't cause overflow or underflow
        assert(sum + arr[index] as i128 <= 2^127 - 1 && sum + arr[index] as i128 >= -2^127) by {
            lemma_sum_to_monotonic(arr@.take((index) as int), arr@);
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