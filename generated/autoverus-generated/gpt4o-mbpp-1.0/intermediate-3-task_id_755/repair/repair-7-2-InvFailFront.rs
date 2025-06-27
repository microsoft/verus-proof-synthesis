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

spec fn min_spec(seq: Seq<i32>) -> int
    recommends
        0 < seq.len(),
    decreases seq.len(),
{
    if seq.len() == 1 {
        seq[0] as int
    } else if seq.len() == 0 {
        0
    } else {
        let later_min = min_spec(seq.drop_first());
        if seq[0] <= later_min {
            seq[0] as int
        } else {
            later_min as int
        }
    }
}

fn second_smallest(numbers: &Vec<i32>) -> (indices: (usize, usize))
    requires
        numbers.len() >= 2,
    ensures
        forall|k: int|
            0 <= k < numbers.len() && k != indices.0 && numbers[indices.0 as int] == min_spec(
                numbers@,
            ) ==> (# [trigger] numbers[k] >= numbers[indices.1 as int]),
        exists|k: int|
            0 <= k < numbers.len() && k != indices.0 && (# [trigger] numbers[k]
                == numbers[indices.1 as int]),
{
    let mut min_index: usize = 0;
    let mut second_min_index: usize = 1;
    if numbers[1] < numbers[0] {
        min_index = 1;
        second_min_index = 0;
    }
    let mut index = 2;
    proof {
        lemma_seq_subrange_all(numbers@);
        assert(numbers[(min_index) as int] == min_spec(numbers@.subrange(0, (index) as int))); // Added by AI
    }
    while index < numbers.len()
        invariant
            2 <= numbers.len(),
            exists|k|
                0 <= k < index && k != min_index ==> numbers[k] == numbers[(
                second_min_index) as int],
            forall|i: int|
                0 <= i < numbers.len() ==> if i != min_index && i != second_min_index {
                    numbers[(second_min_index) as int] <= numbers[i]
                } else {
                    true
                }, // This array is never changed in the loop
            forall|i| 0 <= i < numbers.len() ==> numbers[i] >= numbers[(min_index) as int], // This array is never changed in the loop
            forall|j|
                0 <= j < index && j != min_index ==> numbers[j] >= numbers[(
                second_min_index) as int],
            index <= numbers.len(),
            2 <= index <= numbers.len(),
            forall|k: int|
                0 <= k < index ==> (k == min_index || k == second_min_index || numbers[k]
                    > numbers[(second_min_index) as int] || numbers[k] >= numbers[(
                min_index) as int]),
            forall|k: int|
                0 <= k < index ==> numbers[k] >= numbers[(min_index) as int] || numbers[k]
                    >= numbers[(second_min_index) as int],
            min_index < numbers.len(),
            numbers[(min_index) as int] == min_spec(numbers@.subrange(0, index as int)),
            second_min_index < numbers.len(),
            numbers.len() >= 2,
            proof { // Added by AI
                assert (n == numbers.len()); // Added by AI
            }
    {
        if numbers[index] < numbers[min_index] {
            second_min_index = min_index;
            min_index = index;
        } else if numbers[index] < numbers[second_min_index] {
            second_min_index = index;
        }
        index += 1;
        proof {
            lemma_seq_subrange_ascend(numbers@, 0, ( index ) as int);
            assert(numbers[(min_index) as int] == min_spec(numbers@.subrange(0, index as int))); // Added by AI
        }
    }
    (min_index, second_min_index)
}

} // verus!

//             forall|i: int|
//                 0 <= i < numbers.len() ==> if i != min_index && i != second_min_index {
//                     numbers[(second_min_index) as int] <= numbers[i]
//                 } else {
//                     true
//                 }, // This array is never changed in the loop
//   None: forall|i: int|                 0 <= i < numbers.len() ==> if i != min_index && i != second_min_index {                     numbers[(second_min_index) as int] <= numbers[i]                 } else {                     true                 }

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: True