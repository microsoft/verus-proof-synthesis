use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]
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
        v =~= v.subrange(0, v.len() as int),
{
    assert(v =~= v.subrange(0, v.len() as int));
}

/// Helper function to prove properties of the filter operation
proof fn lemma_seq_filter_append<T>(v: Seq<T>, x: T, pred: FnSpec(T) -> bool)
    ensures
        pred(x) ==> v.push(x).filter(pred) == v.filter(pred).push(x),
        !pred(x) ==> v.push(x).filter(pred) == v.filter(pred),
{
    if pred(x) {
        assert(v.push(x).filter(pred) =~= v.filter(pred).push(x));
    } else {
        assert(v.push(x).filter(pred) =~= v.filter(pred));
    }
}

fn find_odd_numbers(arr: &Vec<u32>) -> (odd_numbers: Vec<u32>)
    ensures
        odd_numbers@ == arr@.filter(|x: u32| x % 2 != 0),
{
    proof {
        reveal(Seq::filter);
    }

    let mut odd_numbers: Vec<u32> = Vec::new();
    let input_len = arr.len();

    let mut index = 0;
    proof {
        assert(odd_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 != 0));
    }
    while index < arr.len()
        invariant
            index <= arr.len(),
            odd_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 != 0),
            0 <= index <= arr.len(),
            arr.len() == input_len,
    {
        if arr[index] % 2 != 0 {
            odd_numbers.push(arr[index]);
        }
        index += 1;

        proof {
            if arr[index - 1] % 2 != 0 {
                lemma_seq_filter_append(arr@.subrange(0, index as int - 1), arr[index - 1], |x: u32| x % 2 != 0);
            }
            assert(odd_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 != 0)); 
        }
    }

    proof {
        lemma_seq_subrange_all(arr@);
    }

    odd_numbers
}

} // verus!

//             assert(odd_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 != 0)); // Added by AI
//   assertion failed: odd_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 != 0)

// Compilation Error: False, Verified: 3, Errors: 2, Verus Errors: 3
// Safe: False