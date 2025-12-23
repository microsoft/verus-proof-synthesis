
use vstd::prelude::*;
fn main() {}

verus! {
proof fn lemma_seq_subrange_all<T>(v: Seq<T>)
    ensures
        v == v.subrange(0, v.len() as int),
{
    assert(v =~= v.subrange(0, v.len() as int));
}

proof fn lemma_seq_subrange_ascend<T>(v: Seq<T>, i:int, j: int)
    requires
        0<= i < j <= v.len(),
    ensures
        v.subrange(i, j as int).drop_last() == v.subrange(i, j-1 ),
{
    assert(v.subrange(i, j as int).drop_last() =~= v.subrange(i, j-1));
}

#[verifier::loop_isolation(false)]
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
            text.len() == text.len(), // Added loop invariant specifying the length of the array
    {
        if ((text[index] as u8) >= 48 && (text[index] as u8) <= 57) {
            count += 1;
        }
        index += 1;
        proof {
            lemma_seq_subrange_ascend(text@, 0, ( index ) as int);
            assert(count_digits_recursively(text@.subrange(0, index as int)) == count);
        }
    }
    proof {
        lemma_seq_subrange_all(text@);
    }
    count
}

} // verus!


// Score: (5, 0)
// Safe: True