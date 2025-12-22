use vstd::prelude::*;

fn main() {
    // Write a function in Rust to extract only the rear index character of each string in the given sequence of strings.

    assert_eq!(
        extract_rear_chars(&vec![
            "Mers".as_bytes().to_vec(),
            "for".as_bytes().to_vec(),
            "Vers".as_bytes().to_vec()
        ]),
        "srs".as_bytes().to_vec()
    );
    assert_eq!(
        extract_rear_chars(&vec![
            "Avenge".as_bytes().to_vec(),
            "for".as_bytes().to_vec(),
            "People".as_bytes().to_vec()
        ]),
        "ere".as_bytes().to_vec()
    );
    assert_eq!(
        extract_rear_chars(&vec![
            "Gotta".as_bytes().to_vec(),
            "get".as_bytes().to_vec(),
            "go".as_bytes().to_vec()
        ]),
        "ato".as_bytes().to_vec()
    );
}

verus! {

fn extract_rear_chars(s: &Vec<Vec<u8>>) -> (result: Vec<u8>)
    requires
        forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i].len() > 0,
    ensures
        s.len() == result.len(),
        forall|i: int| 0 <= i < s.len() ==> result[i] == #[trigger] s[i][s[i].len() - 1],
{
    let mut rear_chars: Vec<u8> = Vec::with_capacity(s.len());
    let mut index = 0;
    while index < s.len()
        invariant
            0 <= index <= s.len(),
            rear_chars.len() == index,
            forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i].len() > 0,
            forall|k: int| 0 <= k < index ==> rear_chars[k] == #[trigger] s[k][s[k].len() - 1],
    {
        let seq = &s[index];
        rear_chars.push(seq[seq.len() - 1]);
        index += 1;
    }
    rear_chars
}

} // verus!
