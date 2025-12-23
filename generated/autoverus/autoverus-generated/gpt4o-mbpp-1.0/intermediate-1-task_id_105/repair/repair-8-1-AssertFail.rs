use vstd::prelude::*;
fn main() {}

verus! {
/*
 This lemma is often useful to put right after a loop that has a loop invariant involving Seq::subrange(0, i), with i being the loop index.
 Example usage:
    while ( k < s.len() )
      invariant
          ...
          k <= s.len(),
          ...s@.subrange(0, k as int)...,
          ...
    {
       ...
       k = k + 1;
    }
    proof{
     	lemma_seq_subrange_all(s@);
    }
 */
proof fn lemma_seq_subrange_all<T>(v: Seq<T>)
    ensures
        v == v.subrange(0, v.len() as int),
{
    assert(v =~= v.subrange(0, v.len() as int));
}

/*
 This lemma is often useful to put near the end of a loop body that has a loop invariant involving Seq::subrange(j, k), with k being the loop index. It will help prove the property of range j..k+1 of a Sequence based on the property held for range j..k of a Sequence.
 Example usage:
    while ( k < s.len() )
      invariant
          ...
          k <= s.len(),
          ...s@.subrange(j, k as int)...,
          ...
    {
       ...
       proof{
       	  lemma_seq_subrange_ascend(s@, j, k+1);
       }
       k = k + 1;
    }
 */
proof fn lemma_seq_subrange_ascend<T>(v: Seq<T>, i:int, j: int)
    requires
        0<= i < j <= v.len(),
    ensures
        v.subrange(i, j as int).drop_last() == v.subrange(i, j-1 ),
{
    assert(v.subrange(i, j as int).drop_last() =~= v.subrange(i, j-1));
}

/*
 The inductive property of counting booleans to help with the loop invariant.
 This proof shows that the boolean count is preserved through any sequence increment.
*/
proof fn lemma_count_boolean_increment(seq: Seq<bool>, count: int, next: bool)
    requires
        count == count_boolean(seq),
    ensures
        count_boolean(seq.push(next)) == count + if next { 1 } else { 0 },
    decreases seq.len(),
{
    assert(count_boolean(seq.push(next)) == count_boolean(seq) + if next { 1 } else { 0 });
}

/*
 Spec function counting boolean values by recursion.
 Uses a decreasing measure on the length of the sequence.
*/
spec fn count_boolean(seq: Seq<bool>) -> int
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_boolean(seq.drop_last()) + if (seq.last()) {
            1 as int
        } else {
            0 as int
        }
    }
}

/*
 Main function for counting true boolean values in vector.
 Uses a while loop to traverse the vector and maintain an invariant.
 The proof block at the end of the loop helps assert the invariant condition.
*/
fn count_true(arr: &Vec<bool>) -> (count: u64)
    ensures
        0 <= count <= arr.len(),
        count_boolean(arr@) == count,
{
    let mut index = 0;
    let mut counter = 0;
    while index < arr.len()
        invariant
            0 <= counter <= index,
            0 <= counter,
            0 <= index <= arr.len(),
            count_boolean(arr@.subrange(0, index as int)) == counter as int,
            index <= arr.len(),
            arr.len() == arr.len(), // Loop Invariant specifying length of arr
            // Adding a loop invariant to cover all elements since `arr` is not modified in the loop.
            forall |k: int| 0 <= k < arr.len() ==> arr@[k] == arr@[k], // added based on observation that arr is never modified within the loop
    {
        if (arr[index]) {
            counter += 1;
        }
        index += 1;
        
        proof {
            if index > 1 {
                lemma_seq_subrange_ascend(arr@, 0, index as int);
            }
            lemma_count_boolean_increment(arr@.subrange(0, index as int - 1), counter as int - if arr@[index as int - 1] { 1 } else { 0 }, arr@[index as int - 1]);
            assert(count_boolean(arr@.subrange(0, index as int)) == counter as int);
        }
    }
    proof {
        lemma_seq_subrange_all(arr@);
    }
    counter
}

} // verus!

//             assert(count_boolean(arr@.subrange(0, index as int)) == counter as int);
//   assertion failed: count_boolean(arr@.subrange(0, index as int)) == counter as int

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: True