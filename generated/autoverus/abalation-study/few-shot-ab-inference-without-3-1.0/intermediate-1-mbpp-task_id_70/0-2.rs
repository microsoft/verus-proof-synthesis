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
    while index < seq.len()
        invariant
            seq.len() > 0,
            1 <= index <= seq.len(),
            forall|i: int| 1 <= i < index ==> seq[i].len() == seq[0].len(),
            forall|i: int, j: int|
                (0 <= i < seq.len() && 0 <= j < seq.len() && i < index && j < index) ==> (#[trigger] seq[i].len()
                == #[trigger] seq[j].len()),
    {
        if ((&seq[index]).len() != (&seq[0]).len()) {
            return false;
        }
        index += 1;
    }
    true
}

} // verus!
// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1