use vstd::prelude::*;

fn main() {}

verus! {

fn find_odd_numbers(arr: &Vec<u32>) -> (odd_numbers: Vec<u32>)
    ensures
        odd_numbers@ == arr@.filter(|x: u32| x % 2 != 0),
{
    let mut odd_numbers: Vec<u32> = Vec::new();
    let input_len = arr.len();

    let mut index = 0;

    proof {
        reveal(Seq::filter);
    }

    assert(odd_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 != 0));

    while index < arr.len()
        invariant
            index <= arr.len(),
            odd_numbers.len() <= index,
            odd_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 != 0),
    {
        if (arr[index] % 2 != 0) {
            odd_numbers.push(arr[index]);
        }
        index += 1;

        proof {
            lemma_seq_subrange_ascend(arr@, 0, index as int);
        }
    }

    proof {
        lemma_seq_subrange_all(arr@);
    }

    odd_numbers
}

} // verus!
// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2