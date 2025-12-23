use vstd::prelude::*;

fn main() {}

verus! {

proof fn lemma_seq_subrange_filter<T>(v: Seq<T>, pred: fn(&T) -> bool, i: int, j: int)
    requires
        0 <= i && i <= j && j <= v.len(),
    ensures
        v.subrange(i, j).filter(( pred ) as FnSpec<(T,), bool>) == v.filter(pred).subrange(i, v.filter(pred).len()),
{
    assert(v.subrange(i, j).filter(pred) =~= v.filter(pred).subrange(i, v.filter(pred).len()));
}

fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
{
    let mut even_numbers: Vec<u32> = Vec::new();
    let mut index = 0;

    assert(even_numbers@ == arr@.subrange(0, index as int).filter(|&x| x % 2 == 0));

    while index < arr.len()
        invariant
            index <= arr.len(),
            even_numbers@ == arr@.subrange(0, index as int).filter(|&x| x % 2 == 0),
    {
        if (arr[index] % 2 == 0) {
            even_numbers.push(arr[index]);
            
            proof {
                lemma_seq_subrange_filter(arr@, |x: &u32| *x % 2 == 0, 0, index as int + 1);
            }
        }
        index += 1;
    }
    even_numbers
}

} // verus!

// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1