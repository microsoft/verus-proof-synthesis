use vstd::prelude::*;

fn main() {}

verus! {

proof fn lemma_seq_subrange_ascend<T>(v: Seq<T>, i: int, j: int)
    requires
        0 <= i < j <= v.len(),
    ensures
        v.subrange(i as int, j - 1 as int).add(seq![v.index(j - 1)]) =~= v.subrange(i as int, j),
{
    assert(v.subrange(i as int, j - 1 as int).add(seq![v.index(j - 1)]) =~= v.subrange(i as int, j));
}

proof fn lemma_seq_subrange_all<T>(v: Seq<T>)
    ensures
        v === v.subrange(0, v.len() as int),
{
    assert(v === v.subrange(0, v.len() as int));
}

#[verifier::loop_invariant]
fn remove_odds(arr: &Vec<u32>) -> (even_list: Vec<u32>)
    ensures
        even_list@ == arr@.filter(|x: u32| x % 2 == 0),
{
    let mut even_list: Vec<u32> = Vec::new();
    let input_len = arr.len();

    let mut index = 0;

    proof {
        reveal(Seq::filter);
    }

    assert(even_list@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0));

    while index < arr.len()
        invariant
            index <= arr.len(),
            even_list@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0),
    {
        if (arr[index] % 2 == 0) {
            even_list.push(arr[index]);
            proof {
                lemma_seq_subrange_ascend(arr@, 0, index as int + 1);
            }
        }
        index += 1;
    }
    
    even_list
}

} // verus!
// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1