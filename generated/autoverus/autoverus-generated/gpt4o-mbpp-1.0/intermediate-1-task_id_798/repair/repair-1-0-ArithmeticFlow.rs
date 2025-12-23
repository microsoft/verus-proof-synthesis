
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

proof fn lemma_sum_to_bounds(arr: Seq<i64>, bound: int)
    requires
        forall|i: int| 0 <= i < arr.len() ==> arr.index(i) < bound && arr.index(i) > -bound,
    ensures
        sum_to(arr) < arr.len() * bound &&
        sum_to(arr) > -arr.len() * bound,
    decreases arr.len(),
{
    if arr.len() > 0 {
        lemma_sum_to_bounds(arr.drop_last(), bound);

        let last = arr.last();
        assert(arr.len() > 0);
        assert(sum_to(arr.drop_last()) + last < arr.drop_last().len() * bound + bound);
        assert(sum_to(arr.drop_last()) + last > -arr.drop_last().len() * bound - bound);
    }
}

fn sum(arr: &Vec<i64>) -> (sum: i128)
    ensures
        sum_to(arr@) == sum,
{
    let mut index = 0;
    let mut sum = 0i128;
    let bound = 1000000i64; // Example bound, modify based on requirements
    
    while index < arr.len()
        invariant
            arr.len() == arr.len(),
            index <= arr.len(),
            sum == sum_to(arr@.subrange(0, index as int)) as i128,
            index < arr.len(),
            arr.len() == arr.len(),
            forall|i: int| 0 <= i < arr.len() ==> arr[i] < bound && arr[i] > -bound,
    {
        let next_value = arr[index] as i128;
        
        // Assertion to check bounds before adding to sum
        assert(sum + next_value < i128::MAX);
        assert(sum + next_value > i128::MIN);
        
        // Alternatively based on seq length and bound
        assert(sum + next_value < (arr.len() as i128) * (bound as i128));
        assert(sum + next_value > -(arr.len() as i128) * (bound as i128));
        
        sum = sum + next_value;
        index += 1;
    }
    sum
}

} // verus!


//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: False, Verified: 1, Errors: 3, Verus Errors: 8
// Safe: False