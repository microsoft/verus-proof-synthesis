use vstd::prelude::*;

fn main() {}

verus! {

proof fn lemma_seq_filter_append<T>(v: Seq<T>, item: T, pred: fn(T) -> bool)
    requires
        pred(item),
    ensures
        v.filter(( pred ) as FnSpec<(T,), bool>).add(seq![item]) == v.add(seq![item]).filter(pred),
{
}

proof fn lemma_seq_filter_no_append<T>(v: Seq<T>, item: T, pred: fn(T) -> bool)
    requires
        !pred(item),
    ensures
        v.filter(pred) == v.add(seq![item]).filter(pred),
{
}

fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
{
    let mut even_numbers: Vec<u32> = Vec::new();
    let mut index = 0;

    proof {
        assert(even_numbers@ == arr@.subrange(0, (index) as int).filter(|x: u32| x % 2 == 0));
    }

    while index < arr.len()
        invariant
            index <= arr.len(),
            even_numbers@ == arr@.subrange(0, (index) as int).filter(|x: u32| x % 2 == 0),
    {
        if arr[index] % 2 == 0 {
            even_numbers.push(arr[index]);
            proof {
                lemma_seq_filter_append(arr@.subrange(0, (index) as int), arr[index], |x: u32| x % 2 == 0);
            }
        } else {
            proof {
                lemma_seq_filter_no_append(arr@.subrange(0, (index) as int), arr[index], |x: u32| x % 2 == 0);
            }
        }
        index += 1;
    }
    even_numbers
}

} // verus!

// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1