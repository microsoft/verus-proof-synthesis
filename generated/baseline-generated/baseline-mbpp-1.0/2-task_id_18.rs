use vstd::prelude::*;

fn main() {}

verus! {

fn contains(str: &Vec<char>, key: char) -> (result: bool)
    ensures
        result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
{
    let mut i = 0;
    while i < str.len()
        invariant
            0 <= i <= str.len(),
            forall |j: int| 0 <= j < i ==> str[j] != key
    {
        if str[i] == key {
            return true;
        }
        i += 1;
    }
    false
}

fn remove_chars(str1: &Vec<char>, str2: &Vec<char>) -> (result: Vec<char>)
    ensures
        forall|i: int|
            0 <= i < result.len() ==> (str1@.contains(#[trigger] result[i]) && !str2@.contains(
                #[trigger] result[i],
            )),
        forall|i: int|
            0 <= i < str1.len() ==> (str2@.contains(#[trigger] str1[i]) || result@.contains(
                #[trigger] str1[i],
            )),
{
    let mut output_str = Vec::new();
    let mut index: usize = 0;

    while index < str1.len()
        invariant
            0 <= index <= str1.len(),
            output_str.len() <= index,
            forall |j: int| 0 <= j < output_str.len() ==> (str1@.contains(#[trigger] output_str[j]) && !str2@.contains(#[trigger] output_str[j])),
            forall |j: int| 0 <= j < index ==> (str2@.contains(#[trigger] str1[j]) || output_str@.contains(#[trigger] str1[j])),
    {
        if !contains(str2, str1[index]) {
            output_str.push(str1[index]);
        }
        index += 1;
    }
    output_str
}

} // verus!
// Score: (3, 1)
// Safe: False