
use vstd::prelude::*;

fn main() {}

verus! {
    #[verifier::loop_isolation(false)]
    fn find_negative_numbers(arr: &Vec<i32>) -> (negative_list: Vec<i32>)
        ensures
            negative_list@ == arr@.filter(|x: i32| x < 0),
    {
        proof {
            reveal(Seq::filter); // Ensure the Seq::filter is revealed before use
        }

        let mut negative_list: Vec<i32> = Vec::new();
        let mut index = 0;

        assert(negative_list@ == arr@.subrange(0, index as int).filter(|x: i32| x < 0)); // Initial assertion

        while index < arr.len()
            invariant
                index <= arr.len(),
                negative_list@ == arr@.subrange(0, index as int).filter(|x: i32| x < 0),
                arr.len() == arr.len(), // Size of arr invariant
        {
            if arr[index] < 0 {
                negative_list.push(arr[index]); // Push negative numbers to the negative_list
            }
            index += 1;
        }

        proof {
            lemma_seq_subrange_all(arr@); // Verifying subranges
        }

        negative_list
    }

    // A proof verifying subrange and drop_last relationships in sequences
    proof fn lemma_seq_subrange_ascend<T>(v: Seq<T>, i: int, j: int)
        requires
            0 <= i < j <= v.len(),
        ensures
            v.subrange(i as int, j as int).drop_last() == v.subrange(i as int, j-1 ),
    {
        assert(v.subrange(i as int, j as int).drop_last() =~= v.subrange(i as int, j-1));
    }

    // A proof verifying that a full range sequence is equal to its subrange of the same span
    proof fn lemma_seq_subrange_all<T>(v: Seq<T>)
        ensures
            v == v.subrange(0, v.len() as int),
    {
        assert(v =~= v.subrange(0, v.len() as int));
    }

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpw8b44fbx`)
// 

// Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 1
// Safe: False