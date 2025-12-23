
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::spec_pub]
spec fn is_subrange_filter(arr: Seq<i32>, index: int, negative_list: Seq<i32>) -> bool {
    negative_list == arr.subrange(0, index).filter(|x: i32| *x < 0)
}

#[verifier::spec_pub]
proof fn lemma_seq_subrange_all<T>(v: Seq<T>)
    ensures
        v =~= v.subrange(0, v.len()),
{
    assert(v === v.subrange(0, v.len()));
}

fn find_negative_numbers(arr: &Vec<i32>) -> (negative_list: Vec<i32>)
    ensures
        negative_list@ == arr@.filter(|x: i32| *x < 0),
{
    let mut negative_list: Vec<i32> = Vec::new();
    let mut index = 0;

    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            is_subrange_filter(arr@, index as int, negative_list@),
            arr.len() == arr.len(),
    {
        if arr[index] < 0 {
            negative_list.push(arr[index]);
        }
        index += 1;
        
        proof {
            let index_ = index as int;
            assert(arr@.filter(|x: i32| *x < 0) =~= arr@.subrange(0, index_).filter(|x: i32| *x < 0));
        }
    }

    proof {
        lemma_seq_subrange_all(arr@);
    }
    
    negative_list
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp7tsu9eu1`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 6
// Safe: False