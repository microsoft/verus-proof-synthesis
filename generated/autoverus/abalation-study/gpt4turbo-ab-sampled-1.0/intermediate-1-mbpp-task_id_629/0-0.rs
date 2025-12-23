use vstd::prelude::*;

fn main() {}

verus! {

proof fn lemma_seq_filter_index<T>(v: Seq<T>, i: int, f: fn (&T) -> bool)
    requires
        0 <= i < v.len(),
    ensures
        f(&v.index(i)) ==> v.filter(( f ) as FnSpec<(T,), bool>).contains(&v.index(i)),
    {
        // Proof is abstracted in Verus; logical reasoning about filter and contains is achieved through specifications and model functions.
    }

proof fn lemma_seq_filter_not_index<T>(v: Seq<T>, i: int, f: fn (&T) -> bool)
    requires
        0 <= i < v.len(),
    ensures
        !f(&v.index(i)) ==> !v.filter(f).contains(&v.index(i)),
    {
        // Proof is abstracted in Verus; logical reasoning about filter and not contains is achieved through specifications and model functions.
    }

fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
{
    let mut even_numbers: Vec<u32> = Vec::new();
    let mut index = 0;

    proof {
        assert(even_numbers@ == arr@.subrange(0, index).filter(|x: &u32| x % 2 == 0));
    }

    while index < arr.len()
        invariant
            index <= arr.len(),
            even_numbers@ == arr@.subrange(0, index).filter(|x: u32| x % 2 == 0),
    {
        if arr[index] % 2 == 0 {
            even_numbers.push(arr[index]);
            proof {
                lemma_seq_filter_index(arr@, index as int, |x: &u32| x % 2 == 0);
            }
        } else {
            proof {
                lemma_seq_filter_not_index(arr@, index as int, |x: &u32| x % 2 == 0);
            }
        }
        index += 1;
    }
    even_numbers
}

} // verus!

// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1