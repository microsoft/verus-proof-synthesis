
#[allow(unused_imports)]
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

spec fn seq_to_set_rec<A>(seq: Seq<A>) -> Set<A>
    decreases seq.len(),
{
    if seq.len() == 0 {
        Set::empty()
    } else {
        seq_to_set_rec(seq.drop_last()).insert(seq.last())
    }
}

fn remove_duplicates(nums: Vec<i32>) -> (res: Vec<i32>)
    ensures
        res@.no_duplicates(),
        nums@.to_set().ext_equal(res@.to_set()),
{
    let mut res = Vec::new();
    let mut i = 0;
    proof {
        assert(i <= nums.len());
        assert(seq_to_set_rec(nums@.subrange(0, i as int)).ext_equal(res@.to_set()));
    }
    while i < nums.len()
        invariant
            i <= nums.len(),
            res@.no_duplicates(),
            seq_to_set_rec(nums@.subrange(0, i as int)).ext_equal(res@.to_set()),
            nums.len() == nums.len(), // Loop invariant specifying the length of nums
            res.len() == res.len(),   // Loop invariant specifying the length of res
    {
        let mut found = false;
        let mut j = 0;
        while j < res.len()
            invariant_except_break
                !found ==> forall|k: int| 0 <= k < j ==> res[k as int] != nums[i as int],
                j <= res.len(),
                i < nums.len(),
                res.len() == res.len(),   // Loop invariant specifying the length of res
                nums.len() == nums.len(), // Loop invariant specifying the length of nums
        {
            if nums[i] == res[j] {
                found = true;
                break;
            }
            j += 1;
        }
        if (!found) {
            res.push(nums[i]);
        }
        i += 1;
        proof {
            lemma_seq_subrange_ascend(nums@, 0, (i) as int);
            assert(seq_to_set_rec(nums@.subrange(0, i as int)).ext_equal(res@.to_set()));
        }
    }
    proof {
        lemma_seq_subrange_all(nums@);
    }
    res
}

} // verus!


//             assert(seq_to_set_rec(nums@.subrange(0, i as int)).ext_equal(res@.to_set()));
//   assertion failed: seq_to_set_rec(nums@.subrange(0, i as int)).ext_equal(res@.to_set())

// Compilation Error: False, Verified: 4, Errors: 2, Verus Errors: 3
// Safe: False