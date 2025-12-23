
use vstd::prelude::*;

fn main() {}

verus! {
    /// Specification functions to check specific properties
    spec fn max_lengths_forall_cond(seq: Seq<Seq<i32>>, max_list: Seq<i32>, index: int) -> bool {
        // Ensuring the `max_list` has length greater than or equivalent to all sequences before `index`
        forall|k: int| 0 <= k < index ==> max_list.len() >= #[trigger] seq[k].len()
    }

    spec fn max_lengths_exists_cond(seq: Seq<Seq<i32>>, max_list: Seq<i32>, index: int) -> bool {
        // Ensuring that `max_list` exists within the list of sequences up till `index`
        exists|m: int| 0 <= m < index && max_list =~= #[trigger] seq[m]
    }

    /// Function to get the maximum length list
    fn max_length_list(seq: &Vec<Vec<i32>>) -> (&Vec<i32>)
        requires
            seq.len() > 0, // Ensuring non-empty sequence list
        ensures
            forall|k: int| 0 <= k < seq.len() ==> max_list.len() >= #[trigger] (seq[k]).len(), // Ensuring the resultant list is at least as long as any other
            exists|k: int| 0 <= k < seq.len() && max_list@ =~= #[trigger] (seq[k]@), // Ensuring the resultant list actually exists in the sequence list
    {
        let mut max_list = &seq[0]; // Initial assumption of maximum as the first sequence
        let mut index = 1; // Starting from the second element
        
        while index < seq.len()
            invariant
                0 <= index <= seq.len(), // Ensuring `index` stays within boundaries
                exists|m: int| 0 <= m < index && max_list@ =~= #[trigger] (seq[m]@), // `max_list` existence invariant within bounds
                forall|k: int| 0 <= k < index ==> max_list.len() >= #[trigger] (seq[k]).len(), // Comparing each sequence length within limits
                seq.len() > 0, // Making sure the sequence list length condition holds throughout
        {
            if (seq[index].len() > max_list.len()) { // Update max_list if a longer sequence is found
                max_list = &seq[index];
            }
            index += 1; // Move to the next sequence
        }

        // Proof block to verify that postconditions are satisfied after the loop ends
        proof {
            assert(forall|k: int| 0 <= k < seq.len() ==> max_list.len() >= #[trigger] seq[k].len());
            assert(exists|k: int| 0 <= k < seq.len() && max_list@ =~= #[trigger] seq[k]@);
        }

        max_list // Returning the maximum length list found
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpdkkjmonb`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False