
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
    assert(v.take(i as int).drop_last()=~=v.take(i-1));
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
    reveal(Seq::filter);

    let input_len = arr.len();
    let mut index = 0;
    while index < arr.len()
        invariant
            arr.len() == input_len,
            arr@.len() == arr.len(),
            arr@.len() == input_len,
            forall|i: int| 0 <= i < index ==> arr[i] % 2 == 0,
            forall|k: int| 0 <= k < arr.len() ==> (if k < index { arr[k] % 2 == 0 } else { true }),
            index <= arr.len(),
            input_len == arr.len(),
    {
        if (arr[index] % 2 != 0) {
            proof {
                lemma_seq_take_all(arr@);
                assert(arr@.take(index as int) == arr@.take(index as int).filter(|x: u32| x % 2 == 0));
                assert(arr[index as int] % 2 != 0);
            }
            return Some(index);
        }
        index += 1;
        proof {
            if index > 0 {
                lemma_seq_take_ascend(arr@, index as int);
            }
        }
    }
    None
}

} // verus!


//                 assert(arr@.take(index as int) == arr@.take(index as int).filter(|x: u32| x % 2 == 0));
//   assertion failed: arr@.take(index as int) == arr@.take(index as int).filter(|x: u32| x % 2 == 0)

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: True