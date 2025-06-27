use vstd::prelude::*;

fn main() {}

verus! {

fn extract_rear_chars(s: &Vec<Vec<char>>) -> (result: Vec<char>)
    requires
        forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i].len() > 0,
    ensures
        s.len() == result.len(),
        forall|i: int| 0 <= i < s.len() ==> result[i] == #[trigger] s[i][s[i].len() - 1],
{
    let mut rear_chars: Vec<char> = Vec::with_capacity(s.len());
    let mut index = 0;
    
    while index < s.len()
        invariant
            index <= s.len(),
            rear_chars.len() == index,
            s.len() == rear_chars.capacity(),
             forall|i: int| 0 <= i < s.len() ==> s[i].len() > 0,
            forall|j: int| 0 <= j < index ==> rear_chars[j] == #[trigger] s[j][s[j].len() - 1],
    {
        let seq = &s[index];
        rear_chars.push(seq[seq.len() - 1]);
        index += 1;
    }
    
    rear_chars
}

} // verus!
// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1