
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

fn sub_array_at_index(main: &Vec<i32>, sub: &Vec<i32>, idx: usize) -> (result: bool)
    requires
        sub.len() <= main.len(),
        0 <= idx <= (main.len() - sub.len()),
    ensures
        result == (main@.subrange(idx as int, (idx + sub@.len())) =~= sub@),
{
    let mut i = 0;
    while i < sub.len()
        invariant
            0 <= idx <= main.len() - sub.len(),
            forall|j: int| 0 <= j < i ==> main[idx + (j as usize)] == sub[j as int],
            i <= sub.len(),
            main.len() == main@.len(),
            sub.len() == sub@.len(),
            0 <= idx <= (main.len() - sub.len()),
    {
        if (main[idx + i] != sub[i]) {
            return false;
        }
        i += 1;
    }
    true
}

fn is_sub_array(main: &Vec<i32>, sub: &Vec<i32>) -> (result: bool)
    requires
        sub.len() <= main.len(),
    ensures
        result == (exists|k: int, l: int|
          0 <= k <= (main.len() - sub.len()) && l == k + sub.len() && (# [trigger] (
            main@.subrange(k, l))) =~= sub@),
{
    if sub.len() > main.len() {
        return false;
    }
    let mut index = 0;
    while index <= (main.len() - sub.len())
        invariant
            forall|k: int, l: int| 0 <= k < index ==> l == k + sub.len() && main@.subrange(k, l) =~= sub@,
            index <= main.len() - sub.len() + 1,
            sub.len() == sub@.len(),
            main.len() == main@.len(),
            0 <= main.len() - sub.len() <= main.len(),
    {
        if (sub_array_at_index(&main, &sub, index)) {
            return true;
        }
        index += 1;
        proof {
            lemma_seq_subrange_ascend(main@, 0, index as int);
        }
    }
    proof {
        lemma_seq_subrange_all(main@);
        assert(forall|k: int, l: int| 0 <= k < index ==> l == k + sub.len() && main@.subrange(k, l) =~= sub@);
    }
    false
}

}


//         assert(forall|k: int, l: int| 0 <= k < index ==> l == k + sub.len() && main@.subrange(k, l) =~= sub@);
//   assertion failed: forall|k: int, l: int| 0 <= k < index ==> l == k + sub.len() && main@.subrange(k, l) =~= sub@

// Compilation Error: False, Verified: 3, Errors: 2, Verus Errors: 3
// Safe: True