
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

spec fn count_identical(s1: Seq<i32>, s2: Seq<i32>, s3: Seq<i32>) -> int
    decreases s1.len(), s2.len(), s3.len(),
{
    if s1.len() == 0 || s2.len() == 0 || s3.len() == 0 {
        0
    } else {
        count_identical(s1.drop_last(), s2.drop_last(), s3.drop_last()) + if (s1.last() == s2.last()
            && s2.last() == s3.last()) {
            1 as int
        } else {
            0 as int
        }
    }
}

fn count_identical_position(arr1: &Vec<i32>, arr2: &Vec<i32>, arr3: &Vec<i32>) -> (count: usize)
    requires
        arr1.len() == arr2.len() && arr2.len() == arr3.len(),
    ensures
        0 <= count <= arr1.len(),
        count_identical(arr1@, arr2@, arr3@) == count,
{
    let mut count = 0;
    let mut index = 0;
    while index < arr1.len()
        invariant
            arr1.len() == arr2.len() && arr2.len() == arr3.len(),
            count <= index,
            index <= arr1.len(),
            count_identical(
                arr1@.subrange(0, index as int),
                arr2@.subrange(0, index as int),
                arr3@.subrange(0, index as int),
            ) == count as int,
    {
        if arr1[index] == arr2[index] && arr2[index] == arr3[index] {
            count += 1;
        }
        index += 1;
        proof {
            lemma_seq_subrange_ascend(arr1@, 0, index as int);
            lemma_seq_subrange_ascend(arr2@, 0, index as int);
            lemma_seq_subrange_ascend(arr3@, 0, index as int);
            assert(count_identical(
                arr1@.subrange(0, index as int),
                arr2@.subrange(0, index as int),
                arr3@.subrange(0, index as int),
            ) == count as int);
        }
    }
    proof {
        lemma_seq_subrange_all(arr1@);
        lemma_seq_subrange_all(arr2@);
        lemma_seq_subrange_all(arr3@);
    }
    count
}

} // verus!


//             assert(count_identical(
//                 arr1@.subrange(0, index as int),
//                 arr2@.subrange(0, index as int),
//                 arr3@.subrange(0, index as int),
//             ) == count as int);
//   assertion failed: count_identical(                 arr1@.subrange(0, index as int),                 arr2@.subrange(0, index as int),                 arr3@.subrange(0, index as int),             ) == count as int

// Compilation Error: False, Verified: 5, Errors: 0, Verus Errors: 0
// Safe: True