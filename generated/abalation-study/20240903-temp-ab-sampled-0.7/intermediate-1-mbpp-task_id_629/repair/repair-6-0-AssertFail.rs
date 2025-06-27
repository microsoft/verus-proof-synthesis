
use vstd::prelude::*;

// Entry point
fn main() {}

verus! {

/*
 This lemma is often useful to put right after a loop that has a loop invariant involving Seq::subrange(0, i), with i being the loop index.
 */
proof fn lemma_seq_subrange_all<T>(v: Seq<T>)
    ensures
        v == v.subrange(0, v.len() as int),
{
    assert(v =~= v.subrange(0, v.len() as int));
}

/*
 This lemma is often useful to put near the end of a loop body that has a loop invariant involving Seq::subrange(j, k), with k being the loop index. It will help prove the property of range j..k+1 of a Sequence based on the property held for range j..k of a Sequence.
 */
proof fn lemma_seq_subrange_ascend<T>(v: Seq<T>, i: int, j: int)
    requires
        0 <= i < j <= v.len(),
    ensures
        v.subrange(i, j as int).drop_last() == v.subrange(i, j-1),
{
    assert(v.subrange(i, j as int).drop_last() =~= v.subrange(i, j-1));
}

#[verifier::loop_isolation(false)]
fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
{
    reveal(Seq::filter); // Added to help Verus understand the filter method

    let mut even_numbers: Vec<u32> = Vec::new();
    let mut index = 0;
    proof {
        assert(even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0)); // Added by AI
    }
    while index < arr.len()
        invariant
            even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0),
            index <= arr.len(),
            arr.len() == arr.len(),
            // The array `arr` is not modified in the loop
            forall |k: int| 0 <= k < arr.len() ==> arr[k] == arr[k],
    {
        if arr[index] % 2 == 0 {
            even_numbers.push(arr[index]);
        }
        index += 1;
        proof {
            // Adding the necessary invocations here
            lemma_seq_subrange_ascend(arr@, 0, index as int);
            assert(even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0)); // Added by AI
        }
    }
    proof {
        lemma_seq_subrange_all(arr@);
        assert(even_numbers@ == arr@.filter(|x: u32| x % 2 == 0)); // Added by AI
    }
    even_numbers
}

} // verus!


//         assert(even_numbers@ == arr@.filter(|x: u32| x % 2 == 0)); // Added by AI
//   assertion failed: even_numbers@ == arr@.filter(|x: u32| x % 2 == 0)

// Compilation Error: False, Verified: 3, Errors: 0, Verus Errors: 0
// Safe: False