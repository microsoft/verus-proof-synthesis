
use vstd::prelude::*;

fn main() {}

verus! {

proof fn lemma_seq_subrange_filter<T>(v: Seq<T>, p: fn(T) -> bool)
    ensures
        v.filter(( p ) as FnSpec<(T,), bool>) == v.filter(p).take_last(v.filter(p).len()).add(v.filter(p).skip(v.filter(p).len())),
    {
        assert(v.filter(p) == v.filter(p).take_last(v.filter(p).len()).add(v.filter(p).skip(v.filter(p).len())));
    }

fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
{
    let mut even_numbers: Vec<u32> = Vec::new();
    let mut index = 0;
    assert(even_numbers@ == arr@.filter(|x: u32| x % 2 == 0).take_last(0));

    while index < arr.len()
        invariant
            index <= arr.len(),
            even_numbers@ == arr@.filter(|x: u32| x % 2 == 0).take_last(index as int),
    {
        if (arr[index] % 2 == 0) {
            even_numbers.push(arr[index]);
        }
        index += 1;

        proof {
            lemma_seq_subrange_filter(arr@, |x: u32| x % 2 == 0);
        }
    }
    even_numbers
}

} // verus!


// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1