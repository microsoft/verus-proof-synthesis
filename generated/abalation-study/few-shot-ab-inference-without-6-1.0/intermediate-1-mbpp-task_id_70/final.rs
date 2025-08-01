
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

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
            seq.len() == seq.len(),
            // Adding invariant to cover every element in the array, as seq is not modified inside the loop
            forall|i: int, j: int| (0 <= i < seq.len() && 0 <= j < seq.len()) ==> (seq[i].len() == seq[j].len()),
    {
        if ((&seq[index]).len() != (&seq[0]).len()) {
            return false;
        }
        index += 1;
    }
    true
}

} // verus!
// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1