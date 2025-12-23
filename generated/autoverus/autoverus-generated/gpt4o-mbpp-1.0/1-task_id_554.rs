use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

proof fn lemma_seq_subrange_ascend<T>(v: Seq<T>, i: int, j: int)
    requires
        0<= i < j <= v.len(),
    ensures
        v.subrange(i as int, j as int).drop_last() == v.subrange(i as int, j-1 ),
{
    assert(v.subrange(i as int, j as int).drop_last() =~= v.subrange(i as int, j-1));
}

proof fn lemma_seq_subrange_all<T>(v: Seq<T>)
    ensures
        v =~= v.subrange(0, v.len() as int),
{
    assert(v =~= v.subrange(0, ( v.len() ) as int));
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
        if (arr[index] % 2 != 0) {
            odd_numbers.push(arr[index]);
        }
        index += 1;

        proof {
            assert(odd_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 != 0)); // Added by AI
            lemma_seq_subrange_ascend(arr@, 0, index as int);
        }
    }

    proof {
        lemma_seq_subrange_all(arr@);
    }

    odd_numbers
}

} // verus!
// Score: (3, 1)
// Safe: True