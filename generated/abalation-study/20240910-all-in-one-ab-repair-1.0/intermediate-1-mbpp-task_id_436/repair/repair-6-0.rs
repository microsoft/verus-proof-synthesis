
use vstd::prelude::*;
fn main() {}

verus! {

spec fn filter_negative(x: i32) -> bool {
    x < 0
}

fn find_negative_numbers(arr: &Vec<i32>) -> (negative_list: Vec<i32>)
    ensures
        negative_list@ == arr@.filter(filter_negative),
{
    proof {
        reveal(Seq::filter);
    }

    let mut negative_list: Vec<i32> = Vec::new();
    let mut index = 0;

    assert(negative_list@ == arr@.subrange(0, index as int).filter(filter_negative));

    while index < arr.len()
        invariant
            index <= arr.len(),
            negative_list@ == arr@.subrange(0, index as int).filter(filter_negative),
            arr.len() == arr.len(),
    {
        if (arr[index] < 0) {
            negative_list.push(arr[index]);
        }
        index += 1;
    }

    proof {
        lemma_seq_subrange_all(arr@);
        assert(negative_list@ == arr@.filter(filter_negative));
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


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp8txfe5s9`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 4
// Safe: False