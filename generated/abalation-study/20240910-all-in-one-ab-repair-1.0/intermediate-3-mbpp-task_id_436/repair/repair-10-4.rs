
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
            0 <= index <= arr.len(),
            negative_list@ == arr@.subrange(0, index as int).filter(|x: i32| x < 0),
            arr.len() == arr.len(),
    {
        if arr[index] < 0 {
            negative_list.push(arr[index]);
            proof {
                assert(negative_list@ == arr@.subrange(0, index as int + 1).filter(|x: i32| x < 0));
            }
        } else {
            proof {
                assert(negative_list@ == arr@.subrange(0, index as int + 1).filter(|x: i32| x < 0));
            }
        }

        index += 1;
    }

    proof {
        lemma_seq_subrange_all(arr@);
        lemma_seq_filter_valid(arr@, negative_list@, |x: i32| x < 0);
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

proof fn lemma_seq_filter_valid<T>(v: Seq<T>, filtered: Seq<T>, pred: FnSpec(T) -> bool)
    requires
        filtered == v.filter(pred),
    ensures
        forall|x: T| filtered.contains(x) ==> v.contains(x) && pred(x),
{
    // This lemma validates the filter relationship between the original and the filtered sequence
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpo3wjgazz`)
// 

// Compilation Error: False, Verified: 3, Errors: 2, Verus Errors: 3
// Safe: False