
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

    assert(negative_list@ == Seq::<i32>::empty());

    while index < arr.len()
        invariant
            index <= arr.len(),
            negative_list@ == arr@.subrange(0, index as int).filter(|x: i32| x < 0),
            arr.len() == arr.len(),
    {
        if arr[index] < 0 {
            let ghost prev_negative_list = negative_list@; // Added by AI
            negative_list.push(arr[index]);
            proof {
                assert(negative_list@ == prev_negative_list.push(arr@[index]));
                assert(negative_list@ == arr@.subrange(0, index as int + 1).filter(|x: i32| x < 0));
            }
        } else {
            proof {
                assert(negative_list@ == arr@.subrange(0, index as int).filter(|x: i32| x < 0));
            }
        }
        index += 1;
    }

    proof {
        lemma_seq_subrange_all(arr@);
    }

    negative_list
}

proof fn lemma_seq_subrange_all<T>(v: Seq<T>)
    ensures
        v == v.subrange(0, v.len() as int),
{
    assert(v =~= v.subrange(0, v.len() as int));
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp7mfip7h1`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False