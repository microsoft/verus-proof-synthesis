use vstd::prelude::*;

fn main() {}

verus! {

proof fn lemma_filter_append<T>(v: Seq<T>, v2: Seq<T>, pred: fn(&T) -> bool)
    ensures
        v.add(v2).filter(( pred ) as FnSpec<(T,), bool>) == v.filter(pred).add(v2.filter(pred)),
{
    assert(v.add(v2).filter(pred) =~= v.filter(pred).add(v2.filter(pred)));
}

fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
{
    let mut even_numbers: Vec<u32> = Vec::new();
    let mut index = 0;
    proof {
        assert(even_numbers@ == arr@.subrange(0, index as int).filter(|&x| x % 2 == 0));
    }
    while index < arr.len() 
        invariant
            index <= arr.len(),
            even_numbers@ == arr@.subrange(0, index as int).filter(|&x| x % 2 == 0),
    {
        if arr[index] % 2 == 0 {
            even_numbers.push(arr[index]);
            proof {
                lemma_filter_append(arr@.subrange(0, index as int), seq![arr[index]], |&x| x % 2 == 0);
            }
        }
        index += 1;
    }
    even_numbers
}

} // verus!


// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1