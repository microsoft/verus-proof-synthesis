use vstd::prelude::*;

fn main() {}

verus! {
fn all_sequence_equal_length(seq: &Vec<Vec<i32>>) -> (result: bool)
    requires
        seq.len() > 0,
    ensures
        result == (forall|i: int, j: int| (0 <= i < seq.len() && 0 <= j < seq.len()) ==> (#[trigger] seq[i].len() == #[trigger] seq[j].len())),
{
    let mut index = 1;
    let len_0 = seq[0].len();
    proof {
        assert forall|i: int, j: int| (0 <= i < 1 && 0 <= j < 1) implies seq[i].len() == seq[j].len() by {
            assert(i == 0 && j == 0);
        };
    }
    while index < seq.len()
        invariant
            1 <= index <= seq.len(),
            len_0 == seq[0].len(),
            forall |k: int| 0 <= k < index ==> seq[k].len() == len_0
    {
        if seq[index].len() != len_0 {
            return false;
        }
        index += 1;
        proof {
            assert forall|k: int| 0 <= k < index implies seq[k].len() == len_0 by {
                if k == index - 1 {
                    assert(seq[k].len() == len_0);
                }
            };
        }
    }
    true
}
} // verus!

// Score: (2, 0)
// Safe: False