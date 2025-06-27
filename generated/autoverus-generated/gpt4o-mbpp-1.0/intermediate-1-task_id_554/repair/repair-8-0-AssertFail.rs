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

proof fn lemma_seq_filter_monotonicity<T>(s: Seq<T>, p: FnSpec(T) -> bool, n: int)
    requires
        0 <= n <= s.len(),
    ensures
        s.subrange(0, n).filter(p) =~= s.take(n).filter(p),
{
    if n == 0 {
        assert(s.subrange(0, n).filter(p) =~= Seq::empty());
        assert(s.take(n).filter(p) =~= Seq::empty());
    } else {
        assert(s.subrange(0, n).drop_last().filter(p) =~= s.take(n - 1).filter(p));
        if p(s.index(n - 1)) {
            assert(s.subrange(0, n).filter(p) =~= s.take(n - 1).filter(p).push(s.index(n - 1)));
        } else {
            assert(s.subrange(0, n).filter(p) =~= s.take(n - 1).filter(p));
        }
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
            lemma_seq_filter_monotonicity(arr@, |x: u32| x % 2 != 0, index as int);
            if arr[index - 1] % 2 != 0 {
                assert(arr@.subrange(0, index as int).filter(|x: u32| x % 2 != 0).last() == arr@[index - 1]);
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

// Compilation Error: False, Verified: 3, Errors: 2, Verus Errors: 5
// Safe: False