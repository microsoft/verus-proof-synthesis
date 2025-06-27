
use vstd::prelude::*;

fn main() {}

verus! {
    fn find_negative_numbers(arr: &Vec<i32>) -> (negative_list: Vec<i32>)
        ensures
            negative_list@ == arr@.filter(|x: i32| x < 0),
    {
        proof {
            reveal(Seq::filter);
        }

        let mut negative_list: Vec<i32> = Vec::new();
        let mut index = 0;

        assert(negative_list@ == arr@.subrange(0, index as int).filter(|x: i32| x < 0));

        while index < arr.len()
            invariant
                index <= arr.len(),
                negative_list@ == arr@.subrange(0, index as int).filter(|x: i32| x < 0),
                arr.len() == arr.len(), // Invariant to confirm that the length doesn't change
        {
            if arr[index] < 0 {
                negative_list.push(arr[index]);
                proof {
                    assert(negative_list@ == arr@.subrange(0, index as int + 1).filter(|x: i32| x < 0)); // Temporarily assert within scope
                }
            }
            index += 1;
            proof {
                assert(negative_list@ == arr@.subrange(0, index as int).filter(|x: i32| x < 0)); // Assert to maintain invariant after increment
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
            v.subrange(i as int, j as int).drop_last() == v.subrange(i as int, j - 1),
    {
        assert(v.subrange(i as int, j as int).drop_last() =~= v.subrange(i as int, j - 1));
    }

    proof fn lemma_seq_subrange_all<T>(v: Seq<T>)
        ensures
            v == v.subrange(0, v.len() as int),
    {
        assert(v =~= v.subrange(0, v.len() as int));
    }

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp21e9l677`)
// 

// Compilation Error: False, Verified: 3, Errors: 1, Verus Errors: 2
// Safe: False