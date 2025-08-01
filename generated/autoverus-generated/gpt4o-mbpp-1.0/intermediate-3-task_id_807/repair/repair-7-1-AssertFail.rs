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

proof fn filter_preserves_even(seq: Seq<u32>, i: int)
    requires
        0 <= i <= seq.len(),
        forall |k: int| 0 <= k < i ==> seq[k] % 2 == 0,
    ensures
        seq.take(i).filter(|x: u32| x % 2 == 0) == seq.take(i)
{
    if i > 0 {
        filter_preserves_even(seq, i - 1);
        if seq[(i - 1) as int] % 2 == 0 {
            assert(seq.take(i).filter(|x: u32| x % 2 == 0) == seq.take(i - 1).push(seq[(i - 1) as int]).filter(|x: u32| x % 2 == 0));
            assert(seq.take(i).filter(|x: u32| x % 2 == 0) == seq.take(i - 1).push(seq[(i - 1) as int]));
        }
    }
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
            forall |k: int| 0 <= k < index ==> (arr[k] % 2 == 0),
            index <= arr.len(),
    {
        if arr[index] % 2 != 0 {
            proof {
                let i = index as int;
                filter_preserves_even(arr@, i);
                assert(arr@.take(i) == arr@.take(i).filter(|x: u32| x % 2 == 0));
                assert(arr[index as int] % 2 != 0);
            }
            return Some(index);
        }
        index += 1;
    }
    None
}
} // verus!




//                 assert(arr@.take(index as int) == arr@.take(index as int).filter(|x: u32| x % 2 == 0));
//   assertion failed: arr@.take(index as int) == arr@.take(index as int).filter(|x: u32| x % 2 == 0)

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False