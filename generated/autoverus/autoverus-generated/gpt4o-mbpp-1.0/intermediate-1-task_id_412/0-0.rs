use vstd::prelude::*;

fn main() {}

verus! {

proof fn lemma_seq_subrange_ascend<T>(v: Seq<T>, i: int, j: int)
    requires
        0 <= i < j <= v.len(),
    ensures
        v.subrange(i, j).drop_last() == v.subrange(i, j - 1),
{
    assert(v.subrange(i, j).drop_last() =~= v.subrange(i, j - 1));
}

proof fn lemma_seq_subrange_all<T>(v: Seq<T>)
    ensures
        v == v.subrange(0, ( v.len() ) as int),
{
    assert(v =~= v.subrange(0, ( v.len() ) as int));
}

fn remove_odds(arr: &Vec<u32>) -> (even_list: Vec<u32>)
    ensures
        even_list@ == arr@.filter(|x: u32| x % 2 == 0),
{
    proof {
        reveal(Seq::filter);
    }

    let mut even_list: Vec<u32> = Vec::new();
    let input_len = arr.len();

    let mut index = 0;

    assert(even_list@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0));

    while index < arr.len()
        invariant
            index <= input_len,
            even_list@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0),
    {
        if arr[index] % 2 == 0 {
            even_list.push(arr[index]);

            proof {
                lemma_seq_subrange_ascend(arr@, 0, index as int + 1);
            }
        }
        
        index += 1;
    }

    proof {
        lemma_seq_subrange_all(arr@);
    }

    even_list
}

} // verus!


// is safe: False
// Score: Compilation Error: False, Verified: 3, Errors: 1, Verus Errors: 2