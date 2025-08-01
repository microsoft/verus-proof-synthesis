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

spec fn sorted_between(a: Seq<u32>, from: int, to: int) -> bool {
    forall|i: int, j: int| from <= i < j < to ==> a[i] <= a[j]
}

spec fn is_reorder_of<T>(r: Seq<int>, p: Seq<T>, s: Seq<T>) -> bool {
    &&& r.len() == s.len()
    &&& forall|i: int| 0 <= i < r.len() ==> 0 <= # [trigger] r[i] < r.len()
    &&& forall|i: int, j: int| 0 <= i < j < r.len() ==> r[i] != r[j]
    &&& p =~= r.map_values(|i: int| s[i])
}

fn test1(nums: &mut Vec<u32>)
    ensures
        sorted_between(nums@, 0, nums@.len() as int),
        exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@),
{
    let n = nums.len();
    if n == 0 {
        proof {
            lemma_seq_subrange_all(nums@);
        }
        return ;
    }
    proof {
        assert(exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@));
    } 
    for i in 1..n
        invariant
            0 <= i <= n,
            exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@.subrange(0, i as int)),
            exists|r: Seq<int>| is_reorder_of(r, nums@.take(i as int), old(nums)@),
            nums.len() == n,
            sorted_between(nums@, 0, i as int),
    {
        let mut j = i;
        proof {
            assert(exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@.subrange(0, i as int)));
        }
        while j != 0
            invariant
                0 <= j <= i,
                exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@.subrange(0, i as int)),
                exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@),
                exists|r: Seq<int>| is_reorder_of(r, nums@.take(i as int), old(nums)@),
                forall|k: int, l: int| 0 <= k < l < n && l < i ==> nums@[k] <= nums@[l],
                forall|k: int| 0 <= k < j ==> nums[k] <= nums[(j) as int],
                i < n,
                j <= i,
                nums.len() == n,
                sorted_between(nums@, 0, i as int),
        {
            if nums[j - 1] > nums[j] {
                let temp = nums[j - 1];
                nums.set(j - 1, nums[j]);
                nums.set(j, temp);
            }
            j -= 1;
        }
        proof {
            assert(exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@.subrange(0, i as int))); // Added by AI
        }
        proof {
            lemma_seq_subrange_ascend(old(nums)@, 0, i as int);
        }
    }
    proof {
        lemma_seq_subrange_all(nums@);
    }
}

} // verus!

//             exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@.subrange(0, i as int)),
//   None: exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@.subrange(0, i as int))

// Compilation Error: False, Verified: 4, Errors: 1, Verus Errors: 4
// Safe: True