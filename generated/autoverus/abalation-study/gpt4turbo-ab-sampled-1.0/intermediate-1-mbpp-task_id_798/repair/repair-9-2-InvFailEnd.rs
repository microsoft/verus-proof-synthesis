
use vstd::prelude::*;
fn main() {}

verus! {

proof fn lemma_seq_subrange_all<T>(v: Seq<T>)
    ensures
        v == v.subrange(0, v.len() as int),
{
    assert(v =~= v.subrange(0, v.len() as int));
}

proof fn lemma_seq_subrange_ascend<T>(v: Seq<T>, i:int, j: int)
    requires
        0<= i < j <= v.len(),
    ensures
        v.subrange(i, j as int).drop_last() == v.subrange(i, j-1 ),
{
    assert(v.subrange(i, j as int).drop_last() =~= v.subrange(i, j-1));
}

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

proof fn lemma_sum_to_bounds(arr: Seq<i64>, additional_value: i64)
    ensures
        sum_to(arr) >= i128::MIN as int && sum_to(arr) + additional_value <= i128::MAX as int,
        sum_to(arr) + additional_value >= i128::MIN as int && sum_to(arr) <= i128::MAX as int
{
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
            sum >= i128::MIN && sum <= i128::MAX,  
            arr.len() == arr@.len(),
            sum == sum_to(arr@.subrange(0, index as int)) as i128,
    {
        proof {
            lemma_sum_to_bounds(arr@.subrange(0, index as int), arr[index as int] as i64);
        }
        
        assert(sum + arr[index as int] as i128 <= i128::MAX && sum + arr[index as int] as i128 >= i128::MIN);
            
        sum = sum + arr[index] as i128;

        index += 1;
        
        proof {
            lemma_seq_subrange_ascend(arr@, 0, ( index ) as int);
        }
    }
    sum
}

}



//             sum == sum_to(arr@.subrange(0, index as int)) as i128,
//   None: sum == sum_to(arr@.subrange(0, index as int)) as i128

// Compilation Error: False, Verified: 4, Errors: 2, Verus Errors: 3
// Safe: True