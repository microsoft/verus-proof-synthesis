
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
                index <= arr.len(),
                negative_list@ == arr@.subrange(0, index as int).filter(|x: i32| x < 0),
        {
            if arr[index] < 0 {
                negative_list.push(arr[index]);
                proof {
                    // Update the invariant proof after inserting a new value.
                    assert(negative_list@ == arr@.subrange(0, (index + 1) as int).filter(|x: i32| x < 0));
                }
            }
            index += 1;
            proof {
                // Reestablish invariants for the next loop iteration.
                assert(negative_list@ == arr@.subrange(0, index as int).filter(|x: i32| x < 0));
            }
        }

        proof {
            lemma_seq_subrange_all(arr@);
        }

        negative_list
    }

    proof fn lemma_seq_subrange_ascend<T>(v: Seq<T>, i: int, j: int)
        requires
            0 <= i < j <= v.len(),
        ensures
            v.subrange(i as int, j as int).drop_last() == v.subrange(i as int, j-1 ),
    {
        assert(v.subrange(i as int, j as int).drop_last() =~= v.subrange(i as int, j-1));
    }

    proof fn lemma_seq_subrange_all<T>(v: Seq<T>)
        ensures
            v == v.subrange(0, v.len() as int),
    {
        assert(v =~= v.subrange(0, v.len() as int));
    }

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpeognkn2z`)
// 

// Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 2
// Safe: False