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
    proof {
        assert(list@.len() > 0);
        assert(0 < n < list@.len());
        assert(0 <= n < list.len());
        assert(index <= list.len());
        assert(list.len() == list.len());
        assert(new_list.len() == index - n);
        assert(new_list@ == list@.subrange(n as int, index as int));
        assert(forall |k: int| 0 <= k < list.len() ==> list[k] == list[k]);
    }
    while index < list.len()
        invariant
            list@.len() > 0,
            0 < n < list@.len(),
            0 <= n < list.len(),
            index <= list.len(),
            list.len() == list.len(),
            new_list.len() == index - n,
            new_list@ == list@.subrange(n as int, index as int),
            forall |k: int| 0 <= k < list.len() ==> list[k] == list[k],
    {
        new_list.push(list[index]);
        index += 1;
        proof {
            lemma_seq_subrange_ascend(list@, n as int, index as int);
            assert(new_list@ == list@.subrange(n as int, index as int)); // Added by AI
        }
    }
    let mut index = 0;
    while index < n
        invariant
            list@.len() > 0,
            0 < n < list@.len(),
            0 <= n < list.len(),
            index <= n,
            list.len() == list.len(),
            new_list.len() == (list.len() - n + index),
            forall |k: int| 0 <= k < list.len() ==> list[k] == list[k],
    {
        new_list.push(list[index]);
        index += 1;
        proof {
            lemma_seq_subrange_all(list@);
            lemma_seq_subrange_ascend(list@, 0, index as int);
        }
    }
    proof {
        lemma_seq_subrange_all(list@);
        assert(new_list@ == list@.subrange(n as int, list@.len() as int).add(list@.subrange(0, n as int))); // Added by AI
    }
    new_list
}

}
// Score: (2, 1)
// Safe: True