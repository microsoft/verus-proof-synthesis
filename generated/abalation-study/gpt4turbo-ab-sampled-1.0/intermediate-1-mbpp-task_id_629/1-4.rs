use vstd::prelude::*;

fn main() {}

verus! {

    proof fn lemma_filter_length<T>(v: Seq<T>, f: proof fn(T) -> bool)
        ensures
            v.filter(f).len() <= v.len(),
    {
        reveal(Seq::<T>::filter);
        assert(v.filter(f).len() <= v.len());
    }

    proof fn lemma_seq_filter_with_condition_appended<T>(v: Seq<T>, x: T, f: proof fn(T) -> bool)
        requires
            f(x),
        ensures
            v.add(seq![x]).filter(f) == v.filter(f).add(seq![x]),
    {
        assert(v.filter(f).add(seq![x]) =~= v.add(seq![x]).filter(f));
    }

    proof fn lemma_seq_filter_without_condition_appended<T>(v: Seq<T>, x: T, f: proof fn(T) -> bool)
        requires
            !f(x),
        ensures
            v.add(seq![x]).filter(f) == v.filter(f),
    {
        assert(v.filter(f) =~= v.add(seq![x]).filter(f));
    }

fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
{
    let mut even_numbers: Vec<u32> = Vec::new();
    let mut index = 0;

    proof {
        lemma_filter_length(arr@, |x: u32| x % 2 == 0);
    }

    assert(even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0));

    while index < arr.len() 
        invariant
            index <= arr.len(),
            even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0),
    {
        if (arr[index] % 2 == 0) {
            proof {
                lemma_seq_filter_with_condition_appended(
                    arr@.subrange(0, index as int),
                    arr[index],
                    |x: u32| x % 2 == 0
                );
            }
            even_numbers.push(arr[index]);
        } else {
            proof {
                lemma_seq_filter_without_condition_appended(
                    arr@.subrange(0, index as int),
                    arr[index],
                    |x: u32| x % 2 == 0
                );
            }
        }
        index += 1;
    }

    proof {
        lemma_filter_length(arr@, |x: u32| x % 2 == 0);
    }

    even_numbers
}

} // verus!
// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1