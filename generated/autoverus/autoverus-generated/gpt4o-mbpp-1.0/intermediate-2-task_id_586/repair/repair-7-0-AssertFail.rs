
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

fn split_and_append(list: &Vec<i32>, n: usize) -> (new_list: Vec<i32>)
    requires
        list@.len() > 0,
        0 < n < list@.len(),
    ensures
        new_list@ == list@.subrange(n as int, list@.len() as int).add(list@.subrange(0, n as int)),
{
    let mut new_list = Vec::new();
    let mut index = n;
    while index < list.len()
        invariant
            forall|i: int| n <= i < index ==> new_list[i - n] == list[i],
            index <= list.len(),
            n < list.len(),
            new_list.len() == index - n,
            0 < n,
            forall |k:int| 0 <= k < list.len() ==> list[k] == list[k], // list is not modified in this loop
    {
        new_list.push(list[index]);
        index += 1;
    }
    let mut index = 0;
    while index < n
        invariant
            forall|i: int| 0 <= i < index ==> new_list[list.len() - n + i] == list[i],
            index <= n,
            new_list.len() == list.len() - n + index,
            0 < n,
            forall |k:int| 0 <= k < list.len() ==> list[k] == list[k], // list is not modified in this loop
    {
        new_list.push(list[index]);
        index += 1;
    }
    proof {
        lemma_seq_subrange_ascend(list@, 0, n as int);
        lemma_seq_subrange_all(list@);
    }
    assert(new_list@ == list@.subrange(n as int, list@.len() as int).add(list@.subrange(0, n as int)));
    new_list
}

} // verus!


//     assert(new_list@ == list@.subrange(n as int, list@.len() as int).add(list@.subrange(0, n as int)));
//   assertion failed: new_list@ == list@.subrange(n as int, list@.len() as int).add(list@.subrange(0, n as int))

// Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 1
// Safe: True