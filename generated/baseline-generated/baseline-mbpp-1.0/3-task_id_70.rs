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
    let first_length = seq[0].len();
    while index < seq.len()
        invariant
            1 <= index <= seq.len(),
            seq.len() > 0, // preserve original requirement
            first_length == seq[0].len(), // preserve initial length
            forall|i: int| (0 <= i < index) ==> seq[i].len() == first_length
    {
        if seq[index].len() != first_length {
            return false;
        }
        index += 1;
    }
    true
}

} // verus!
// Score: (2, 0)
// Safe: False