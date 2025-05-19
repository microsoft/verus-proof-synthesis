use vstd::prelude::*;

fn main() {
    // Write a function in Rust to find the first repeated character in a given string.

    assert_eq!(
        first_repeated_char(&("abcabc".chars().collect())),
        Some((0, 'a'))
    );
    assert_eq!(first_repeated_char(&("abc".chars().collect())), None);
    assert_eq!(
        first_repeated_char(&("123123".chars().collect())),
        Some((0, '1'))
    );
}

verus! {

pub open spec fn count_frequency_rcr(seq: Seq<char>, key: char) -> int
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_frequency_rcr(seq.drop_last(), key) + if (seq.last() == key) {
            1 as int
        } else {
            0 as int
        }
    }
}

fn count_frequency(arr: &Vec<char>, key: char) -> (frequency: usize)
    ensures
        count_frequency_rcr(arr@, key) == frequency,
{
    let mut index = 0;
    let mut counter = 0;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            0 <= counter <= index,
            count_frequency_rcr(arr@.subrange(0, index as int), key) == counter,
        decreases
            arr.len() - index,
    {
        if (arr[index] == key) {
            counter += 1;
        }
        index += 1;
        assert(arr@.subrange(0, index - 1 as int) == arr@.subrange(0, index as int).drop_last());
    }
    assert(arr@ == arr@.subrange(0, index as int));
    counter
}

fn first_repeated_char(str1: &Vec<char>) -> (repeated_char: Option<(usize, char)>)
    ensures
        if let Some((idx, rp_char)) = repeated_char {
            &&& str1@.take(idx as int) =~= str1@.take(idx as int).filter(
                |x: char| count_frequency_rcr(str1@, x) <= 1,
            )
            &&& count_frequency_rcr(str1@, rp_char) > 1
        } else {
            forall|k: int|
                0 <= k < str1.len() ==> count_frequency_rcr(str1@, #[trigger] str1[k]) <= 1
        },
{
    let input_len = str1.len();
    assert(str1@.take(0int).filter(|x: char| count_frequency_rcr(str1@, x) > 1) == Seq::<
        char,
    >::empty());
    let mut index = 0;
    while index < str1.len()
        invariant
            0 <= index <= str1.len(),
            str1@.take(index as int) =~= str1@.take(index as int).filter(
                |x: char| count_frequency_rcr(str1@, x) <= 1,
            ),
        decreases
            str1.len() - index,
    {
        if count_frequency(&str1, str1[index]) > 1 {
            return Some((index, str1[index]));
        }
        assert(str1@.take((index + 1) as int).drop_last() == str1@.take(index as int));
        reveal(Seq::filter);
        index += 1;
    }
    assert(str1@ =~= str1@.take(input_len as int));
    assert(forall|k: int|
        0 <= k < str1.len() ==> count_frequency_rcr(str1@, #[trigger] str1[k]) <= 1);
    None
}

} // verus!
