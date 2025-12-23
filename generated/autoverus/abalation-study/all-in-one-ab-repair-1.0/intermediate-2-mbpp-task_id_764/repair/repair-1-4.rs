
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
            count_digits_recursively(text@.subrange(0, index as int)) == count,
            index <= text.len(),
            text.len() == text.len(),
    {
        if ((text[index] as u8) >= 48 && (text[index] as u8) <= 57) {
            count += 1;
        }
        index += 1;
        proof {
            assert(0 <= count <= index);
            // This invariant states that up to the current index, the count 
            // of digits matches the result of calling count_digits_recursively 
            // on the subrange of text from 0 to index.
            assert(count_digits_recursively(text@.subrange(0, index as int)) == count);
        }
    }
    count
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpkztl7tq6`)
// 

// Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 2
// Safe: True