use vstd::prelude::*;

fn main() {
    // Write a function in Rust to count number of digits in a given string.

    assert_eq!(count_digits(&("program2bedone".chars().collect())), 1);
    assert_eq!(count_digits(&("3wonders".chars().collect())), 1);
    assert_eq!(count_digits(&("123".chars().collect())), 3);
    assert_eq!(count_digits(&("3wond-1ers2".chars().collect())), 3);
}

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
            count == count_digits_recursively(text@.subrange(0, index as int)),
        decreases
            text.len() - index,
    {
        if ((text[index] as u8) >= 48 && (text[index] as u8) <= 57) {
            count += 1;
        }
        index += 1;
        assert(text@.subrange(0, index - 1 as int) == text@.subrange(0, index as int).drop_last());
    }
    assert(text@ == text@.subrange(0, index as int));
    count
}

} // verus!
