use vstd::prelude::*;

fn main() {}

verus! {
proof fn lemma_seq_filter_append<T>(v: Seq<T>, f: fn(&T) -> bool, val: T)
    requires
        f(&val),
    ensures
        v.filter(( f ) as FnSpec<(T,), bool>).add(seq![val]) == (v.add(seq![val])).filter(f),
{
    assert(v.filter(f).add(seq![val]) =~= (v.add(seq![val])).filter(f));
}

proof fn lemma_seq_filter_no_append<T>(v: Seq<T>, f: fn(&T) -> bool, val: T)
    requires
        !f(&val),
    ensures
        v.filter(f) == (v.add(seq![val])).filter(f),
{
    assert(v.filter(f) =~= (v.add(seq![val])).filter(f));
}

fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
{
    let mut even_numbers: Vec<u32> = Vec::new();
    let mut index = 0;

    assert(even_numbers@.len() == 0);
    assert(even_numbers@ == arr@.subrange(0, (index) as int).filter(|x: u32| x % 2 == 0));

    while (index < arr.len())
        invariant
            index <= arr.len(),
            even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0),
    {
        if (arr[index] % 2 == 0) {
            proof {
                lemma_seq_filter_append(arr@.subrange(0, index as int), |x: &u32| *x % 2 == 0, arr[index]);
            }
            even_numbers.push(arr[index]);
        } else {
            proof {
                lemma_seq_filter_no_append(arr@.subrange(0, index as int), |x: &u32| *x % 2 == 0, arr[index]);
            }
        }
        index += 1;
    }
    even_numbers
}

} // verus!

// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1