
use vstd::prelude::*;

fn main() {}

verus! {

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

fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
{
    proof {
        reveal(Seq::filter);
    }

    let mut even_numbers: Vec<u32> = Vec::new();
    let mut index = 0;

    while index < arr.len()
        invariant
            index <= arr.len(),
            forall |k: int| 0 <= k < arr.len() ==> arr[k] == arr[k],                // Ensuring the property holds for every element
            even_numbers.len() == even_numbers.len(), // Invariant specifying length of even_numbers
            even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0),
    {
        if (arr[index] % 2 == 0) {
            even_numbers.push(arr[index]);
            proof {
                lemma_seq_subrange_ascend(arr@, 0, index as int + 1);
            }
        }
        index += 1;
    }

    proof {
        lemma_seq_subrange_all(arr@);
    }

    even_numbers
}

} // verus!
