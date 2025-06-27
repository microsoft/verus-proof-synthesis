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
    let mut index = 1;
    let seq_0_len = seq[0].len(); 

    while index < seq.len()
        invariant
            index <= seq.len(),
            forall|k: int| 0 <= k < index ==> seq[k].len() == seq_0_len,
            seq.len() > 0,
    {
        if seq[index].len() != seq[0].len() {
            return false;
        }
        index += 1;
    }
    true
}

} // verus!

// is safe: False
// Score: Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 1