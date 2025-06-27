use vstd::prelude::*;
fn main() {}

verus! {

spec fn is_upper_case(c: char) -> bool {
    c >= 'A' && c <= 'Z'
}

spec fn shift32_spec(c: char) -> char {
    ((c as u8) + 32) as char
}

spec fn is_lower_case(c: char) -> bool {
    c >= 'a' && c <= 'z'
}

spec fn shift_minus_32_spec(c: char) -> char {
    ((c as u8) - 32) as char
}

spec fn to_toggle_case_spec(s: char) -> char {
    if is_lower_case(s) {
        shift_minus_32_spec(s)
    } else if is_upper_case(s) {
        shift32_spec(s)
    } else {
        s
    }
}

fn to_toggle_case(str1: &Vec<char>) -> (toggle_case: Vec<char>)
    ensures
        str1@.len() == toggle_case@.len(),
        forall|i: int|
            0 <= i < str1.len() ==> toggle_case[i] == to_toggle_case_spec(#[trigger] str1[i]),
{
    let mut toggle_case = Vec::with_capacity(str1.len());
    let mut index = 0;
    while index < str1.len() {
        if (str1[index] >= 'a' && str1[index] <= 'z') {
            toggle_case.push(((str1[index] as u8) - 32) as char);
        } else if (str1[index] >= 'A' && str1[index] <= 'Z') {
            toggle_case.push(((str1[index] as u8) + 32) as char);
        } else {
            toggle_case.push(str1[index]);
        }
        index += 1;

    }
    toggle_case
}

} // verus!
