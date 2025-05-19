use vstd::prelude::*;

fn main() {
    // Write a function in Rust to check whether all the characters are same or not.

    assert_eq!(
        replace_with_colon(&("Python language, Programming language.".chars().collect()))
            .iter()
            .collect::<String>(),
        "Python:language::Programming:language:"
    );
    assert_eq!(
        replace_with_colon(&("a b c,d e f".chars().collect()))
            .iter()
            .collect::<String>(),
        "a:b:c:d:e:f"
    );
    assert_eq!(
        replace_with_colon(&("ram reshma,ram rahim".chars().collect()))
            .iter()
            .collect::<String>(),
        "ram:reshma:ram:rahim"
    );
}

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
            0 <= index <= str1.len(),
            result@.len() == index,
            forall|k: int|
                0 <= k < index ==> #[trigger] result[k] == (if is_space_comma_dot_spec(str1[k]) {
                    ':'
                } else {
                    str1[k]
                }),
        decreases
            str1.len() - index,
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
