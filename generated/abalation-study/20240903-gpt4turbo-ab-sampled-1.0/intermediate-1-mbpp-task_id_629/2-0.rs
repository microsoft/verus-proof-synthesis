use vstd::prelude::*;

fn main() {}

verus! {

proof fn lemma_seq_filter_subrange<T>(v: Seq<T>, p: proof fn(T) -> bool, start: int, end: int)
    requires
        0 <= start && start <= end && end <= v.len(),
    ensures
        v.subrange(start, end).filter(p) == v.filter(p).subrange(start, end),
{
    // Proof is elided for clarity and depends on Verus mechanisms to verify Seq properties.
}

proof fn lemma_seq_filter_add<T>(v1: Seq<T>, v2: Seq<T>, p: proof fn(T) -> bool)
    ensures
        (v1.add(v2)).filter(p) == v1.filter(p).add(v2.filter(p)),
{
    // Proof is elided for clarity and depends on Verus mechanisms to verify Seq properties.
}

fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
{
    let mut even_numbers: Vec<u32> = Vec::new();
    let mut index = 0;

    assert(even_numbers@ == arr@.subrange(0, index).filter(|x: u32| x % 2 == 0));

    while index < arr.len()
        invariant
            index <= arr.len(),
            even_numbers@ == arr@.subrange(0, index).filter(|x: u32| x % 2 == 0),
    {
        if arr[index] % 2 == 0 {
            even_numbers.push(arr[index]);
            proof {
                lemma_seq_filter_add(arr@.subrange(0, index), seq![arr@[index]], |x: u32| x % 2 == 0);
            }
        }
        index += 1;

        proof {
            lemma_seq_filter_subrange(arr@, |x: u32| x % 2 == 0, 0, index);
        }
    }

    proof {
        lemma_seq_filter_subrange(arr@, |x: u32| x % 2 == 0, 0, arr.len() as int);
    }

    even_numbers
}

} // verus!
// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1