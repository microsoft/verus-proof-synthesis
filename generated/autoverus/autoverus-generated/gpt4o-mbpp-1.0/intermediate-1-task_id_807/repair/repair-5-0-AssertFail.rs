
use vstd::prelude::*;
fn main() {}
verus! {
/*
 This lemma is often useful to put right after a loop that has a loop invariant involving Seq::take(i), with i being the loop index.
 Example usage:
    while ( k < s.len() )
      invariant
          ...
          k <= s.len(),
          ...s@.take(k as int)...,
          ...
    {
       ...
       k = k + 1;
    }
	lemma_seq_take_all(s@);
*/
proof fn lemma_seq_take_all<T>(v: Seq<T>)
    ensures
        v == v.take(v.len() as int),
{
    assert(v =~= v.take(v.len() as int));
}


/*
 This lemma is often useful to put near the end of a loop body that has a loop invariant involving Seq::take(i), with i being the loop index.
 Example usage:
    while ( k < s.len() )
      invariant
          ...
          k <= s.len(),
          ...s@.take(k as int)...,
          ...
    {
       ...
       k = k + 1;
       proof{
        lemma_seq_take_ascend(s@, k as int);
       }
    }
*/
proof fn lemma_seq_take_ascend<T>(v: Seq<T>, i: int)
    requires
        0 < i <= v.len(),
    ensures
        v.take(i as int).drop_last() == v.take(i-1),
{
    assert(v.take(i as int).drop_last() =~= v.take(i-1));
}

#[verifier::loop_isolation(false)]
fn find_first_odd(arr: &Vec<u32>) -> (index: Option<usize>)
    ensures
        if let Some(idx) = index {
            &&& arr@.take(idx as int) == arr@.take(idx as int).filter(|x: u32| x % 2 == 0)
            &&& arr[idx as int] % 2 != 0
        } else {
            forall|k: int| 0 <= k < arr.len() ==> (arr[k] % 2 == 0)
        },
{
    // Reveal the implementation of `Seq::filter` to Verus so that it can understand its behavior:
    reveal(Seq::filter);

    let input_len = arr.len();
    let mut index = 0;
    while index < arr.len()
        invariant
            arr@.len() == input_len,
            // The array `arr` is never changed in the loop, thus the invariant should cover every element.
            forall|k: int| 0 <= k < arr.len() ==> ((k < index ==> arr[k] % 2 == 0) && (k >= index ==> true)),
            index <= arr.len(),
            arr.len() == input_len,
    {
        if (arr[index] % 2 != 0) {
            proof {
                lemma_seq_take_all(arr@);
                assert(arr@.take(index as int).filter(|x: u32| x % 2 == 0) == arr@.take(index as int));

                assert(arr[index as int] % 2 != 0);
            }            
            return Some(index);
        }
        index += 1;
        proof {
            let idx = index as int;
            if idx > 0 && idx <= arr@.len() {
                lemma_seq_take_ascend(arr@, idx);
            }
        }
    }

    proof {
        assert(forall|k: int| 0 <= k < arr.len() ==> (arr[k] % 2 == 0));
    }

    None
}

} // verus!


//                 assert(arr@.take(index as int).filter(|x: u32| x % 2 == 0) == arr@.take(index as int));
//   assertion failed: arr@.take(index as int).filter(|x: u32| x % 2 == 0) == arr@.take(index as int)

// Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 1
// Safe: True