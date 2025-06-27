
use vstd::prelude::*;
fn main() {}

verus! {

spec fn is_digit(c: char) -> bool {
    (c as u8) >= 48 && (c as u8) <= 57
}

spec fn count_digits_recursively(seq: Seq<char>) -> int
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_digits_recursively(seq.drop_last()) + if is_digit(seq.last()) {
            1 as int
        } else {
            0 as int
        }
    }
}

fn count_digits(text: &Vec<char>) -> (count: usize)
    ensures
        0 <= count <= text.len(),
        count_digits_recursively(text@) == count,
{
    let mut count = 0;
    let mut index = 0;
    while index < text.len()
        invariant
            0 <= count <= index,
            0 <= count, // Added invariant ensuring `count` is non-negative
            count_digits_recursively(text@.subrange(0, index as int)) == count,
            index <= text.len(),
            text.len() == text.len(),
    {
        if is_digit(text[index]) {
            count += 1;
        }
        index += 1;
        
        proof {
            // Ensure that the invariants hold after every iteration
            assert(0 <= count <= index);
            let sub_seq = text@.subrange(0, index as int);

            if is_digit(text[index - 1]) {
                assert(count_digits_recursively(sub_seq) == count);
            } else {
                assert(count_digits_recursively(sub_seq) == count);
            }
        }
    }
    proof {
        // Ensure final condition matches the recursive function definition
        assert(count_digits_recursively(text@) == count);
    }
    count
}
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpn7fxxwmc`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False