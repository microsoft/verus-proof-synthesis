
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

#[verifier::loop_isolation(false)]
fn find_negative_numbers(arr: &Vec<i32>) -> (negative_list: Vec<i32>)
    ensures
        negative_list@ == arr@.filter(|x: i32| x < 0),
{
    proof {
        // Instruct Verus to reveal the inner workings of Seq::filter
        reveal(Seq::filter);
    }

    // Initialize the negative_list vector
    let mut negative_list: Vec<i32> = Vec::new();
    let mut index = 0;

    // Assert the initial invariant holds before the loop starts
    assert(negative_list@ == arr@.subrange(0, index as int).filter(|x: i32| x < 0));

    while index < arr.len()
        invariant
            index <= arr.len(),
            negative_list@ == arr@.subrange(0, index as int).filter(|x: i32| x < 0),
            arr.len() == arr.len(),
    {
        if arr[index] < 0 {
            // Append the negative number to the negative_list
            negative_list.push(arr[index]);
        }

        // Advance the index
        index += 1;

        proof {
            // Reestablish the loop invariant after each loop iteration
            lemma_seq_subrange_ascend(arr@, 0, index as int);
            assert(negative_list@ == arr@.subrange(0, index as int).filter(|x: i32| x < 0));
        }
    }

    proof {
        // Confirm that the final value of negative_list equals the filter applied to the entire array
        lemma_seq_subrange_all(arr@);
    }

    // Return the list of negative numbers
    negative_list
}


} // verus!


//             assert(negative_list@ == arr@.subrange(0, index as int).filter(|x: i32| x < 0));
//   assertion failed: negative_list@ == arr@.subrange(0, index as int).filter(|x: i32| x < 0)

// Compilation Error: False, Verified: 3, Errors: 0, Verus Errors: 0
// Safe: False