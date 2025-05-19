use vstd::prelude::*;

fn main() {
    // Write a function in Rust to extract only the rear index character of each string in the given sequence of strings.

    assert_eq!(
        extract_rear_chars(&vec![
            "Mers".chars().collect(),
            "for".chars().collect(),
            "Vers".chars().collect()
        ])
        .iter()
        .collect::<String>(),
        "srs"
    );
    assert_eq!(
        extract_rear_chars(&vec![
            "Avenge".chars().collect(),
            "for".chars().collect(),
            "People".chars().collect()
        ])
        .iter()
        .collect::<String>(),
        "ere"
    );
    assert_eq!(
        extract_rear_chars(&vec![
            "Gotta".chars().collect(),
            "get".chars().collect(),
            "go".chars().collect()
        ])
        .iter()
        .collect::<String>(),
        "ato"
    );
}

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
            0 <= index <= s.len(),
            rear_chars.len() == index,
            forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i].len() > 0,
            forall|k: int| 0 <= k < index ==> rear_chars[k] == #[trigger] s[k][s[k].len() - 1],
        decreases
            s.len() - index,
    {
        let seq = &s[index];
        rear_chars.push(seq[seq.len() - 1]);
        index += 1;
    }
    rear_chars
}

} // verus!
