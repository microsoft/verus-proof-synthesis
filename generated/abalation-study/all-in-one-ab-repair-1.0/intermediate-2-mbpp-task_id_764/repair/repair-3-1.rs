
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
        count_digits_recursively(seq.subrange(0, seq.len() - 1)) + if is_digit(seq.index(seq.len() - 1)) {
            1 as int
        } else {
            0 as int
        }
    }
}

fn count_digits(text: &Vec<char>) -> (count: usize)
    ensures
        0 <= count <= text.len(),
        count_digits_recursively(text@) == count as int,
{
    let mut count: usize = 0;
    let mut index: usize = 0;
    while index < text.len()
        invariant
            0 <= count <= index,
            count_digits_recursively(text@.subrange(0, index as int)) == count as int,
            index <= text.len(),
            text.len() == text.len(),
    {
        if is_digit(text[index]) {
            count += 1;
        }
        index += 1;
        proof {
            assert(0 <= count && count <= index);
            assert(index <= text.len());

            // Maintain the invariant relating to the recursive function
            assert(count_digits_recursively(text@.subrange(0, index as int)) == count as int);
        }
    }
    count
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpq4evaw57`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False