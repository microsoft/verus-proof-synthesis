use vstd::prelude::*;

fn main() {}

verus! {

spec fn is_space_comma_dot_spec(c: char) -> bool {
    (c == ' ') || (c == ',') || (c == '.')
}

fn replace_with_colon(str1: &Vec<char>) -> (result: Vec<char>)
    ensures
        str1@.len() == result@.len(),
        forall|k: int|
            0 <= k < result.len() ==> #[trigger] result[k] == (if is_space_comma_dot_spec(str1[k]) {
                ':'
            } else {
                str1[k]
            }),
{
    let mut result: Vec<char> = Vec::with_capacity(str1.len());
    let mut index = 0;
    while index < str1.len()
        invariant
            index <= str1.len(),
            result.len() == index,
            forall|k: int| 0 <= k < index ==> #[trigger] result[k] == (if is_space_comma_dot_spec(str1[k]) {
                ':'
            } else {
                str1[k]
            }),
    {
        if ((str1[index] == ' ') || (str1[index] == ',') || (str1[index] == '.')) {
            result.push(':');
        } else {
            result.push(str1[index]);
        }
        index += 1;
    }
    result
}

} // verus!
// Score: (2, 0)
// Safe: True