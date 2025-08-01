
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
     	reader
ection_eq_seq_subrange_all(ser);
scope {
}
}
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

proof fn lemma_seq_subrange_ascend<T>(v: Seq<T>, i: int, j: int)
    requires
        0 <= i < j <= v.len(),
    ensures
        v.subrange(i, j as int).drop_last() == v.subrange(i, j-1 ),
{
    assert(v.subrange(i, j as int).drop_last() =~= v.subrange(i, j-1));
}

#[verifier::loop_isolation(false)]

proof fn lemma_seq_subrange_ascend<T>(v: Seq<T>, i: int, j: int)
    requires
        0 <= i < j <= v.len(),
    ensures
        v.subrange(i as int, j as int).drop_last() == v.subrange(i as int, j-1),
{
    assert(v.subrange(i as int, j as int).drop_last() =~= v.subrange(i as int, j-1));
}

proof fn lemma_seq_subrange_all<T>(v: Seq<T>)
    ensures
        v == v.subrange(0, v.len() as int),
{
    assert(v =~= v.subrange(0, v.len() as int));
}

fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
{
    // Reveal the filter method to Verus.
    proof {
        reveal(Seq::filter);
    }

    let mut even_numbers: Vec<u32> = Vec::new();
    let mut index = 0;

    // Initial condition assertion
    proof {
        assert(even_numbers@ == arr@.subrange(0, 0).filter(|x: u32| x % 2 == 0)); // Added by AI
    }

    while index < arr.len()
        invariant
            index <= arr.len(),
            forall |k: int| 0 <= k < arr.len() ==> arr[k] == arr[k],                // Ensuring the property holds for every element
            even_numbers.len() == even_numbers.len(), // Invariant specifying length of even_numbers
            even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0),
    {
        if arr[index] % 2 == 0 {
            even_numbers.push(arr[index]);
            proof {
                lemma_seq_subrange_ascend(arr@, 0, index as int + 1);
            }
        }
        index += 1;
        // Reassert after index increase step
        proof {
            assert(even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0)); // Added by AI
        }
    }

    // Final condition proof
    proof {
        lemma_seq_subrange_all(arr@);
        assert(even_numbers@ == arr@.filter(|x: u32| x % 2 == 0)); // Added by AI
    }

    even_numbers
}

}


//             assert(even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0)); // Added by AI
//   assertion failed: even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0)

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False