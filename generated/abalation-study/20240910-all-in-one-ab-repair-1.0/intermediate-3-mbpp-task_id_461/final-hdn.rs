
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_isolation(false)]
    spec fn is_lower_case(c: char) -> bool {
        (c as u32) >= 97 && (c as u32) <= 122
    }

    spec fn is_upper_case(c: char) -> bool {
        (c as u32) >= 65 && (c as u32) <= 90
    }

    spec fn count_uppercase_recursively(seq: Seq<char>) -> int
        decreases seq.len(),
    {
        if seq.len() == 0 {
            0
        } else {
            count_uppercase_recursively(seq.drop_last()) + if is_upper_case(seq.last()) {
                1 as int
            } else {
                0 as int
            }
        }
    }

    fn count_uppercase(text: &Vec<char>) -> (count: u64)
        ensures
            0 <= count <= text.len(),
            count_uppercase_recursively(text@) == count,
    {
        let mut index = 0;
        let mut count = 0;
        while index < text.len()
            invariant
                0 <= count && count <= index,
                0 <= index && index <= text.len(),
                text.len() == text.len(),
                count_uppercase_recursively(text@.take(index as int)) == count as int,
                // Added invariant: All characters in the array are either lower case or upper case
                    0 <= k < text.len() ==> is_lower_case(text[k]) || is_upper_case(text[k]),
        {
            if ((text[index] as u32) >= 65 && (text[index] as u32) <= 90) {
                count += 1;
            }
            index += 1;

            proof {
                // These proofs are to ensure invariants hold after modification
                assert(0 <= count);
                assert(count <= index);
                assert(0 <= index && index <= text.len());
                assert(forall |k: int| 0 <= k < text.len() ==> is_lower_case(text[k]) || is_upper_case(text[k]));
            }
        }
        count
    }
}


// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 3