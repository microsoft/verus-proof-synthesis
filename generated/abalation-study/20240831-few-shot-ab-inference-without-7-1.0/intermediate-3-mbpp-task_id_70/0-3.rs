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
    let initial_len = seq[0].len();

    while index < seq.len()
        invariant
            1 <= index <= seq.len(),
            seq.len() > 0,
            forall|i: int| 0 <= i < index ==> seq[i].len() == initial_len,
    {
        if ((&seq[index]).len() != initial_len) {
            return false;
        }
        index += 1;
    }
    true
}

} // verus!
// is safe: False
// Score: Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 1