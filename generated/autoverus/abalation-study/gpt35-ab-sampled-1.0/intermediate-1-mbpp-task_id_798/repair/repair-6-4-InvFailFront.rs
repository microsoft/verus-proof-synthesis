
fn sum(arr: &Vec<i64>) -> (sum: i128)
    ensures
        sum_to(arr@) == sum,
{
    let mut index = 0;
    let mut sum = 0i128;

    // Add the loop invariant as an assertion before the loop
    assert(forall |k:int| 0 <= k < arr.len() ==> sum_to(arr@.subrange(0, k as int)) == sum_to(arr@.subrange(0, index as int))) by {
      // Add any necessary supporting code to ensure the invariant holds true before the loop
    }

    while index < arr.len()
        invariant
            index <= arr.len(),
            forall |k:int| 0 <= k < arr.len() ==> sum_to(arr@.subrange(0, k as int)) == sum_to(arr@.subrange(0, index as int)),
    {
        assert(sum + arr[( index ) as int] as i128 <= i128::MAX) by{
            lemma_monotonic_sum_to(arr@, 0, index as int);
        }
        assert(sum + arr[( index ) as int] as i128 >= i128::MIN) by{
            lemma_monotonic_sum_to(arr@, 0, index as int);
        }
        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}


//             forall |k:int| 0 <= k < arr.len() ==> sum_to(arr@.subrange(0, k as int)) == sum_to(arr@.subrange(0, index as int)),
//   None: forall |k:int| 0 <= k < arr.len() ==> sum_to(arr@.subrange(0, k as int)) == sum_to(arr@.subrange(0, index as int))

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False