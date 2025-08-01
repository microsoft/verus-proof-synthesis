use vstd::prelude::*;

fn main() {}

verus! {

proof fn lemma_filter_tail<T>(v: Seq<T>, f: proof fn(&T) -> bool, i: int)
    requires
        0 <= i <= v.len(),
    ensures
        v.filter(f) == v.subrange(0, i).filter(f).add(v.subrange(i, v.len()).filter(f)),
{
    assert(v.filter(f) =~= v.subrange(0, i).filter(f).add(v.subrange(i, v.len()).filter(f)));
}

fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
{
    let mut even_numbers: Vec<u32> = Vec::new();
    let mut index = 0;

    proof {
        lemma_filter_tail(arr@, |x: &u32| *x % 2 == 0, 0);
    }

    while index < arr.len()
        invariant
            even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0),
            index <= arr.len(),
    {
        if (arr[index] % 2 == 0) {
            even_numbers.push(arr[index]);
        }
        index += 1;

        proof {
            lemma_filter_tail(arr@, |x: &u32| *x % 2 == 0, index as int);
        }
    }
    even_numbers
}

} // verus!
// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1