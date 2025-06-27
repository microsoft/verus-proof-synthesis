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
    reveal(Seq::filter); // This line is added to help Verus understand filter
    let mut even_numbers: Vec<u32> = Vec::new();
    let mut index = 0;
    proof {
        lemma_seq_subrange_all(arr@);
    }
    while index < arr.len()
        invariant
            even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0),
            index <= arr.len(),
    {
        if (arr[index] % 2 == 0) {
            even_numbers.push(arr[index]);
        }
        proof {
            lemma_seq_subrange_ascend(arr@, 0, index + 1);
        }
        index += 1;
    }
    even_numbers
}
} // verus!

//             even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0),
//   None: even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0)

// Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 1
// Safe: True