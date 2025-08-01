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
    let first_len = seq[0].len();
    while index < seq.len() 
        invariant
            1 <= index <= seq.len(),
            first_len == seq[0].len(),
            forall|i: int| 1 <= i < index ==> seq[i].len() == first_len
    {
        if seq[index].len() != first_len {
            return false;
        }
        index += 1;
    }
    true
}

} // verus!
// Score: (2, 0)
// Safe: False