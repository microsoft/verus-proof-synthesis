

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
            0 <= index <= arr.len(),
            negative_list@ == arr@.subrange(0, index as int).filter(|x: i32| x < 0),
            arr.len() == arr.len(),
    {
        if (arr[index] < 0) {
            negative_list.push(arr[index]);
        }

        proof {
            // Ensure invariant is maintained after the push operation
            assert(negative_list@ == {
                let mut subrange = arr@.subrange(0, index as int).filter(|x: i32| x < 0);
                if arr[index] < 0 {
                    subrange = subrange.push(arr[index]);
                }
                subrange
            });

            lemma_seq_push_filter(arr@, index as int, |x: i32| x < 0);
        }

        index += 1;

        proof {
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

proof fn lemma_seq_push_filter<T>(v: Seq<T>, i: int, f: FnSpec(T) -> bool)
    requires
        0 <= i < v.len(),
    ensures
        v.subrange(0, i).filter(f).push(v[i]) == v.subrange(0, i + 1).filter(f),
{
    if f(v[i]) {
        assert(v.subrange(0, i).filter(f).push(v[i]) =~= v.subrange(0, i + 1).filter(f));
    } else {
        assert(v.subrange(0, i).filter(f) =~= v.subrange(0, i + 1).filter(f));
    }
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp1dwvkubv`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: True