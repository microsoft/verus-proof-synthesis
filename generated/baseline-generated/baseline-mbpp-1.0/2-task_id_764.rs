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
            0 <= index <= text.len(),
            0 <= count <= index,
            count == count_digits_recursively(text@.take(index as int)),
    {
        if ((text[index] as u8) >= 48 && (text[index] as u8) <= 57) {
            count += 1;
        }
        index += 1;
    }
    
    proof {
        assert(count_digits_recursively(text@) == count_digits_recursively(text@.take(index as int)));
        assert(count_digits_recursively(text@.take(index as int)) == count);
    }
    
    count
}

} // verus!

// Score: (1, 2)
// Safe: True