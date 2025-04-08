use vstd::prelude::*;

fn main() {}

verus! {

spec fn is_space_comma_dot_spec(c: u8) -> bool {
    (c == 32) || (c == 44) || (c == 46)
}

fn replace_with_colon(str1: &[u8]) -> (result: Vec<u8>)
    ensures
        str1@.len() == result@.len(),
        forall|k: int|
            0 <= k < result.len() ==> #[trigger] result[k] == (if is_space_comma_dot_spec(str1[k]) {
                58
            } else {
                str1[k]
            }),
{
    let mut result: Vec<u8> = Vec::with_capacity(str1.len());
    let mut index = 0;
    while index < str1.len() {
        if ((str1[index] == 32) || (str1[index] == 44) || (str1[index] == 46)) {
            result.push(58);
        } else {
            result.push(str1[index]);
        }
        index += 1;
    }
    result
}

} // verus!
