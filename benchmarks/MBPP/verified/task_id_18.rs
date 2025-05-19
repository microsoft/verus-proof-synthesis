use vstd::prelude::*;

fn main() {
    // Write a function in Rust to remove characters from the first string which are present in the second string.

    assert_eq!(
        remove_chars(
            &("probasscurve".chars().collect()),
            &("pros".chars().collect())
        )
        .iter()
        .collect::<String>(),
        "bacuve"
    );
    assert_eq!(
        remove_chars(
            &("digitalindia".chars().collect()),
            &("talent".chars().collect())
        )
        .iter()
        .collect::<String>(),
        "digiidi"
    );
    assert_eq!(
        remove_chars(
            &("exoticmiles".chars().collect()),
            &("toxic".chars().collect())
        )
        .iter()
        .collect::<String>(),
        "emles"
    );
}

verus! {

proof fn lemma_vec_push<T>(vec: Seq<T>, i: T, l: usize)
    requires
        l == vec.len(),
    ensures
        forall|k: int| 0 <= k < vec.len() ==> #[trigger] vec[k] == vec.push(i)[k],
        vec.push(i).index(l as int) == i,
{
}

fn contains(str: &Vec<char>, key: char) -> (result: bool)
    ensures
        result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
{
    let mut i = 0;
    while i < str.len()
        invariant
            forall|m: int| 0 <= m < i ==> (str[m] != key),
        decreases
            str.len() - i,
    {
        if (str[i] == key) {
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
    let ghost mut output_len: int = 0;

    while index < str1.len()
        invariant
            forall|k: int|
                0 <= k < output_str.len() ==> (str1@.contains(#[trigger] output_str[k])
                    && !str2@.contains(#[trigger] output_str[k])),
            forall|k: int|
                0 <= k < index ==> (str2@.contains(#[trigger] str1[k]) || output_str@.contains(
                    #[trigger] str1[k],
                )),
        decreases
            str1.len() - index,
    {
        if (!contains(str2, str1[index])) {
            proof {
                lemma_vec_push(output_str@, str1[index as int], output_str.len());
                output_len = output_len + 1;
            }
            output_str.push(str1[index]);
        }
        index += 1;
    }
    output_str
}

} // verus!
