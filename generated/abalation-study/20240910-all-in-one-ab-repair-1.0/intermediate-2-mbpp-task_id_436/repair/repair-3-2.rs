
use vstd::prelude::*;

fn main() {}

verus! {
    #[verifier::loop_isolation(false)]
    fn find_negative_numbers(arr: &Vec<i32>) -> (negative_list: Vec<i32>)
        ensures
            negative_list@ == arr@.filter(|x: i32| x < 0),
    {
        proof {
            reveal(Seq::filter);
        }

        let mut negative_list: Vec<i32> = Vec::new();
        let mut index = 0;

        proof {
            assert(negative_list@ == arr@.subrange(0, index as int).filter(|x: i32| x < 0));
        }

        while index < arr.len()
            invariant
                index <= arr.len(), // Index should be within the length of array.
                arr.len() == arr.len(), // Array length remains unchanged.
                negative_list@ == arr@.subrange(0, index as int).filter(|x: i32| x < 0),
        {
            if arr[index] < 0 {
                negative_list.push(arr[index]);
            }
            index += 1;
            proof {
                // Check if `negative_list` invariant is still held.
                assert(negative_list@ == arr@.subrange(0, index as int).filter(|x: i32| x < 0));
            }
        }

        proof {
            lemma_seq_subrange_all(arr@); // Assert entire array is equal to its subrange
        }

        negative_list
    }

    // Proof function to better handle subrange assertions for verification
    proof fn lemma_seq_subrange_ascend<T>(v: Seq<T>, i: int, j: int)
        requires
            0 <= i < j <= v.len(),
        ensures
            v.subrange(i as int, j as int).drop_last() == v.subrange(i as int, j - 1),
    {
        assert(v.subrange(i as int, j as int).drop_last() =~= v.subrange(i as int, j - 1));
    }

    // Proof function to validate whole sequence equals to subrange from 0 to its length
    proof fn lemma_seq_subrange_all<T>(v: Seq<T>)
        ensures
            v == v.subrange(0, v.len() as int),
    {
        assert(v =~= v.subrange(0, v.len() as int));
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp_k051pg6`)
// 

// Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 1
// Safe: False