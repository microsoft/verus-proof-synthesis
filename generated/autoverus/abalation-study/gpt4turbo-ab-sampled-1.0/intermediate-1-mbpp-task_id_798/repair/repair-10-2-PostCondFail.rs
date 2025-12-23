
sum == sum_to(arr@.subrange(0, index as int)) as i128,


// failed this postcondition
//         sum_to(arr@) == sum,
// at the end of the function body
// {
//     let mut index = 0;
//     let mut sum = 0i128;
//     while index < arr.len()
// ...
//     sum
// }
//   at the end of the function body: {     let mut index = 0;     let mut sum = 0i128;     while index < arr.len()         invariant             index <= arr.len(),             sum >= i128::MIN && sum <= i128::MAX,               arr.len() == arr@.len(),             sum == sum_to(arr@.subrange(0, index as int)) as i128,     {         proof {             lemma_sum_to_bounds(arr@.subrange(0, index as int), arr[index as int] as i64);         }                  assert(sum + arr[index as int] as i128 <= i128::MAX && sum + arr[index as int] as i128 >= i128::MIN);                      sum = sum + arr[index] as i128;          index += 1;                  proof {             lemma_seq_subrange_ascend(arr@, 0, ( index ) as int);         }     }     sum }
//   failed this postcondition: sum_to(arr@) == sum

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False