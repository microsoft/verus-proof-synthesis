use vstd::prelude::*;

fn main() {}

verus! {

proof fn lemma_seq_subrange_even<T>(v: Seq<T>, i: int, j: int)
    requires
        0 <= i < j <= v.len(),
    ensures
        v.subrange(i, j).filter(|&x: &T| x % 2 == 0) == v.subrange(i, j-1).filter(|&x: &T| x % 2 == 0).add(v.index(j-1)).filter(|&x: &T| x % 2 == 0),
{
    assert(v.subrange(i, j).filter(|&x: &T| x % 2 == 0) =~= v.subrange(i, j-1).filter(|&x: &T| x % 2 == 0).add(v.index(j-1)).filter(|&x: &T| x % 2 == 0));
}

proof fn lemma_seq_subrange_start_even<T>(v: Seq<T>, j: int)
    requires
        0 <= j <= v.len(),
    ensures
        v.subrange(0, j).filter(|&x: &T| x % 2 == 0) == v.filter(|&x: &T| x % 2 == 0).subrange(0, v.filter(|&x: &T| x % 2 == 0).len()),
{
    assert(v.subrange(0, j).filter(|&x: &T| x % 2 == 0) =~= v.filter(|&x: &T| x % 2 == 0).subrange(0, v.filter(|&x: &T| x % 2 == 0).len()));
}

fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
{
    let mut even_numbers: Vec<u32> = Vec::new();
    let mut index = 0;

    assert(even_numbers@ == arr@.subrange(0, index as int).filter(|&x: u32| x % 2 == 0));

    while index < arr.len() 
        invariant
            even_numbers@ == arr@.subrange(0, index as int).filter(|&x: u32| x % 2 == 0),
            index <= arr.len(),
    {
        if (arr[index] % 2 == 0) {
            even_numbers.push(arr[index]);
        }
        index += 1;

        proof {
            lemma_seq_subrange_even(arr@, 0, index as int);
        }
    }

    proof {
        lemma_seq_subrange_start_even(arr@, arr.len() as int);
    }
    
    even_numbers
}

} // verus!
// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 30