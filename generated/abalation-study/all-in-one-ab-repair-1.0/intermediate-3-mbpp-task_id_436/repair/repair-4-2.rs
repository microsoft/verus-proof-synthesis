
use vstd::prelude::*;

fn main() {}

verus! {

fn find_negative_numbers(arr: &Vec<i32>) -> (negative_list: Vec<i32>)
    ensures
        negative_list@ == arr@.filter(|x: i32| x < 0),
{
    // Proof to reveal the filter function's behavior
    proof {
        reveal(Seq::filter);
    }

    let mut negative_list: Vec<i32> = Vec::new();
    let mut index = 0;

    // Assert initial invariant
    assert(negative_list@ == arr@.subrange(0, index as int).filter(|x: i32| x < 0));

    while index < arr.len()
        invariant
            index <= arr.len(),
            negative_list@ == arr@.subrange(0, index as int).filter(|x: i32| x < 0),
            arr.len() == arr.len(),
    {
        if arr[index] < 0 {
            negative_list.push(arr[index]);
        }
        // Update index and maintain invariant after push
        proof {
            assert({
                index + 1 <= arr.len()
                ==> negative_list@ == arr@.subrange(0, (index + 1) as int).filter(|x: i32| x < 0)
            });
        }
        index += 1;
        // Maintain the invariant for the entire loop body
        assert({
            index as int <= arr.len() as int
            && negative_list@ == arr@.subrange(0, index as int).filter(|x: i32| x < 0)
        });
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


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp0t1fzl2y`)
// 

// Compilation Error: False, Verified: 3, Errors: 1, Verus Errors: 1
// Safe: False