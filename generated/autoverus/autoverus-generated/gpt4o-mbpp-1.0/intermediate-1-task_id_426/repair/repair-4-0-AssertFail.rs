
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

fn filter_odd_numbers(arr: &Vec<u32>) -> (odd_list: Vec<u32>)
    ensures
        odd_list@ == arr@.filter(|x: u32| x % 2 != 0),
{
    proof {
        reveal(Seq::filter);
    }
    let mut odd_list: Vec<u32> = Vec::new();
    let input_len = arr.len();
    let mut index = 0;
    proof {
        lemma_seq_subrange_all(arr@); // Invoke lemma_seq_subrange_all here
        assert(odd_list@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 != 0)); // Added by AI
    }
    while index < arr.len()
        invariant
            index <= arr.len(),
            odd_list@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 != 0),
            arr.len() == input_len,
    {
        if arr[index] % 2 != 0 {
            odd_list.push(arr[index]);
        }
        index += 1;
        proof {
            lemma_seq_subrange_ascend(arr@, 0, index as int); // Invoke lemma_seq_subrange_ascend here
            assert(odd_list@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 != 0)); // Added by AI
        }
    }
    odd_list
}

}


//             assert(odd_list@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 != 0)); // Added by AI
//   assertion failed: odd_list@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 != 0)

// Compilation Error: False, Verified: 3, Errors: 0, Verus Errors: 0
// Safe: False