use vstd::prelude::*;

fn main() {}

verus! {

fn all_sequence_equal_length(seq: &Vec<Vec<i32>>) -> (result: bool)
    requires
        seq.len() > 0,
    ensures
        result == (forall|i: int, j: int|
            (0 <= i < seq.len() && 0 <= j < seq.len()) ==> (#[trigger] seq[i].len()
                == #[trigger] seq[j].len())),
{
    let len_0 = seq[0].len();
    let mut index = 1;
    while index < seq.len()
        invariant
            index <= seq.len(),
            seq.len() > 0,
            forall | k: int | 0 <= k < index ==> seq[k].len() == len_0,
    {
        if ((&seq[index]).len() != len_0) {
            return false;
        }
        index += 1;
    }
    true
}

} // verus!

// is safe: False
// Score: Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 1