use vstd::prelude::*;

fn main() {}
verus! {

spec fn is_ascii_digit_spec(c: char) -> bool {
    c == '0' || c == '1' || c == '2' || c == '3' || c == '4' || c == '5' || c == '6' || c == '7'
        || c == '8' || c == '9'
}

fn is_ascii_digit(c: char) -> (r: bool)
    ensures
        r == is_ascii_digit_spec(c),
{
    c == '0' || c == '1' || c == '2' || c == '3' || c == '4' || c == '5' || c == '6' || c == '7'
        || c == '8' || c == '9'
}

spec fn all_digits_spec(s: Seq<char>) -> bool {
    forall|i: nat| #![auto] i < s.len() ==> is_ascii_digit_spec(s[i as int])
}

fn all_digits(s: String) -> (result: bool)
    requires
        s.is_ascii(),
    ensures
        all_digits_spec(s@) == result,
{
    let mut result = true;
    let mut i = 0;
    while i < s.as_str().unicode_len()
        invariant
            i <= s.as_str().unicode_len(),
            result == all_digits_spec(s@.subrange(0, i as int)),
            s@.len() == s.as_str().unicode_len(),
    {
        if !is_ascii_digit(s.as_str().get_char(i)) {
            return false;
        }
        i += 1;
    }
    result
}

} // verus!
// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1