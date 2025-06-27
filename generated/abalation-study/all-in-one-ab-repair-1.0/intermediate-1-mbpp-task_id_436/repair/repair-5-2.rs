
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

    assert(negative_list@ == arr@.subrange(0, index as int).filter(|x: i32| x < 0));

    while index < arr.len()
        invariant
            index <= arr.len(),
            negative_list@ == arr@.subrange(0, index as int).filter(|x: i32| x < 0),
            arr.len() == old(arr).len(), // Added the invariant to keep track of original array length
    {
        if arr[index] < 0 {
            negative_list.push(arr[index]);
            proof {
                let r = Seq::new(negative_list@.len(), |i: int| i); // Added by AI, for assertion fail
                assert(is_reorder_of(r, negative_list@, negative_list@)); // Added by AI, for assertion fail
                assert(exists|r: Seq<int>| is_reorder_of(r, negative_list@, negative_list@));
            }
        }
        index += 1;
    }

    proof {
        lemma_seq_subrange_all(arr@);
        // Additional assertion to help with postcondition verification
        assert(negative_list@ == arr@.subrange(0, index as int).filter(|x: i32| x < 0));
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



// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpl3gmpqvi`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False