
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

proof fn lemma_sum_to_monotonic(smaller: Seq<i64>, larger: Seq<i64>)
    requires
        smaller.len() <= larger.len(),
        smaller == larger.take(( smaller.len() ) as int),
    ensures
        sum_to(smaller) <= sum_to(larger),
{
    // Proof that sum_to is monotonic
    let len_smaller = smaller.len();
    let len_larger = larger.len();
    if len_smaller < len_larger {
        lemma_sum_to_monotonic(smaller, larger.drop_last());
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
            sum == sum_to(arr@.take(index as int)),
            sum_to(arr@.take(index as int)) <= sum_to(arr@),
            index >= 0,
            arr.len() >= 0,
    {
        let current_element = arr[index] as i128;
        
        // Ensure that adding the current element won't cause overflow/underflow
        assert(sum + current_element <= sum_to(arr@) && sum + current_element >= sum_to(arr@.take(index as int)) ) by {
            lemma_sum_to_monotonic(arr@.take(index as int), arr@.take((index as int) + 1));
        };
        
        sum = sum + current_element;
        index += 1;
    }
    sum
}

}



//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False