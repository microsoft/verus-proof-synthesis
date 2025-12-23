
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
            // The invariant is about the count and recursive function result. 
            // We need to show that the condition holds in each step of the loop.
            assert(index <= text.len());
            let sub_seq = text@.subrange(0, index as int);
            if is_digit(text[index - 1]) {
                assert(count_digits_recursively(sub_seq) == count);
            } else {
                assert(count_digits_recursively(sub_seq) == count);
            }
        }
    }
    count
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpv12b7udg`)
// 

// Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 3
// Safe: True