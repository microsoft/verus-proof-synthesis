
use vstd::prelude::*;
fn main() {}

verus! {

proof fn lemma_seq_subrange_all<T>(v: Seq<T>)
    ensures
        v == v.subrange(0, v.len() as int),
{
    assert(v =~= v.subrange(0, v.len() as int));
}

proof fn lemma_seq_subrange_ascend<T>(v: Seq<T>, i:int, j: int)
    requires
        0<= i < j <= v.len(),
    ensures
        v.subrange(i, j as int).drop_last() == v.subrange(i, j-1 ),
{
    assert(v.subrange(i, j as int).drop_last() =~= v.subrange(i, j-1));
}
    #[verifier::loop_isolation(false)]

    fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
        ensures
            even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
    {
        let mut even_numbers: Vec<u32> = Vec::new();
        let mut index = 0;
        proof {
            reveal(Seq::filter); // Allow Verus to understand the filter operation
            assert(even_numbers@ == arr@.subrange(0, 0).filter(|x: u32| x % 2 == 0));
            lemma_seq_subrange_all(arr@);
        }
        while index < arr.len()
            invariant
                even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0),
                index <= arr.len(),
                even_numbers.len() == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0).len(),
                arr.len() == arr@.len(),
        {
            if (arr[index] % 2 == 0) {
                even_numbers.push(arr[index]);
            }
            index += 1;
            proof {
                reveal(Seq::filter);
                lemma_seq_subrange_all(arr@);
                lemma_seq_subrange_ascend(arr@, 0, index as int);
                assert(even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0));
                assert(even_numbers.len() == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0).len());
            }
        }
        even_numbers
    }
}

// Score: (3, 0)
// Safe: True