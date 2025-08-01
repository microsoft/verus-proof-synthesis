use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

proof fn lemma_seq_subrange_ascend<T>(v: Seq<T>, i: int, j: int)
    requires
        0 <= i < j <= v.len(),
    ensures
        v.subrange(i as int, j as int).drop_last() == v.subrange(i as int, j-1),
{
    assert(v.subrange(i as int, j as int).drop_last() =~= v.subrange(i as int, j-1));
}

proof fn lemma_seq_subrange_all<T>(v: Seq<T>)
    ensures
        v == v.subrange(0, v.len() as int),
{
    assert(v =~= v.subrange(0, v.len() as int));
}

proof fn seq_filter_push_eq<T>(s: Seq<T>, f: FnSpec(T) -> bool, x: T)
    requires
        f(x) == true,
    ensures
        s.push(x).filter(f) =~= s.filter(f).push(x)
{
}

proof fn seq_filter_not_contains<T>(s: Seq<T>, f: FnSpec(T) -> bool, x: T)
    requires
        f(x) == false,
    ensures
        s.push(x).filter(f) =~= s.filter(f)
{
}

fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
{
    proof {
        reveal(Seq::filter);
    }

    let mut even_numbers: Vec<u32> = Vec::new();
    let mut index = 0;

    proof {
        assert(even_numbers@ == arr@.subrange(0, 0).filter(|x: u32| x % 2 == 0));
    }

    while index < arr.len()
        invariant
            index <= arr.len(),
            forall |k: int| 0 <= k < arr.len() ==> arr[k] == arr[k],
            even_numbers.len() == even_numbers.len(),
    {
        if (arr[index] % 2 == 0) {
            even_numbers.push(arr[index]);
            proof {
                lemma_seq_subrange_ascend(arr@, 0, index as int + 1);
                let sub_filtered = arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0);
                seq_filter_push_eq(sub_filtered, |x: u32| x % 2 == 0, arr@[index as int]);
            }
        }
        index += 1;
        proof {
        }
    }

    proof {
        lemma_seq_subrange_all(arr@);
    }

    even_numbers
}
}

// Score: Compilation Error: False, Verified: 3, Errors: 3, Verus Errors: 3