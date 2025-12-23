
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

proof fn lemma_seq_take_filter_even<T>(v: Seq<T>, i: int, filter: FnSpec(T) -> bool)
    requires
        0 <= i <= v.len(),
        forall|k: int| 0 <= k < i ==> filter(v.index(k)),
    ensures
        v.take(i as int) == v.take(i as int).filter(filter),
{
    assert(v.filter(filter).take(i as int) == v.take(i as int).filter(filter));
    assert(v.take(i as int) =~= v.filter(filter).take(i as int));
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
    reveal(Seq::filter); // Add this line to help Verus understand `filter`

    let input_len = arr.len();
    let mut index = 0;
    while index < arr.len()
        invariant
            arr.len() == input_len,
            forall|k: int| 0 <= k < arr.len() ==> (k < index ==> (arr[k] % 2 == 0)), // The array `arr` is never changed in the loop.
            index <= arr.len(),
    {
        if (arr[index] % 2 != 0) {
            proof {
                lemma_seq_take_all(arr@);
                lemma_seq_take_ascend(arr@, index as int + 1);
                lemma_seq_take_filter_even(arr@, index as int, |x: u32| x % 2 == 0);
                assert(arr@.take(index as int) == arr@.take(index as int).filter(|x: u32| x % 2 == 0));
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

// Compilation Error: False, Verified: 3, Errors: 1, Verus Errors: 2
// Safe: True