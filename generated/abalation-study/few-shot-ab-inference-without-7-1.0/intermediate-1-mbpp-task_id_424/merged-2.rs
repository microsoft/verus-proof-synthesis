use vstd::prelude::*;
fn main() {}
verus! {

fn extract_rear_chars(s: &Vec<Vec<char>>) -> (result: Vec<char>)
    requires
        forall|i: int| 0 <= i < s.len() ==> # [trigger] s[i].len() > 0,
    ensures
        s.len() == result.len(),
        forall|i: int| 0 <= i < s.len() ==> result[i] == # [trigger] s[i][s[i].len() - 1],
{
    let mut rear_chars: Vec<char> = Vec::with_capacity(s.len());
    let mut index = 0;
    while index < s.len()
        invariant
            forall|i: int|
                0 <= i < index ==> # [trigger] rear_chars[i] == # [trigger] s[i][s[i].len() - 1],
            forall|i: int| 0 <= i < index ==> # [trigger] s[i].len() > 0,
            forall|i: int| 0 <= i < index ==> rear_chars[i] == # [trigger] s[i][s[i].len() - 1],
            index <= s.len(),
            rear_chars.len() == index,
    {
        let seq = &s[index];
        rear_chars.push(seq[seq.len() - 1]);
        index += 1;
    }
    rear_chars
}

} // verus!


// Score: Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 5