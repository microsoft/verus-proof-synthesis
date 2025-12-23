
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
        proof {
            lemma_seq_push_filter(arr@, index as int, |x: i32| x < 0);
        } // Moved proof block before push

        if arr[index] < 0 {
            negative_list.push(arr[index]);
        }

        index += 1;

        proof {
            assert(negative_list@ == arr@.subrange(0, index as int).filter(|x: i32| x < 0));
        }
    }

    negative_list
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


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpzw7cg2x3`)
// 

// Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 5
// Safe: False