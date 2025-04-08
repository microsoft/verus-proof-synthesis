use vstd::prelude::*;

fn main() {
    // Write a function in Rust to find the first repeated character in a given string.

    assert_eq!(first_repeated_char(b"abcabc"), Some((0, b'a')));
    assert_eq!(first_repeated_char(b"abc"), None);
    assert_eq!(first_repeated_char(b"123123"), Some((0, b'1')));
}

verus! {

pub open spec fn count_frequency_rcr(seq: Seq<u8>, key: u8) -> int
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

fn count_frequency(arr: &[u8], key: u8) -> (frequency: usize)
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

fn first_repeated_char(str1: &[u8]) -> (repeated_char: Option<(usize, u8)>)
    ensures
        if let Some((idx, rp_char)) = repeated_char {
            &&& str1@.take(idx as int) =~= str1@.take(idx as int).filter(
                |x: u8| count_frequency_rcr(str1@, x) <= 1,
            )
            &&& count_frequency_rcr(str1@, rp_char) > 1
        } else {
            forall|k: int|
                0 <= k < str1.len() ==> count_frequency_rcr(str1@, #[trigger] str1[k]) <= 1
        },
{
    let input_len = str1.len();
    assert(str1@.take(0int).filter(|x: u8| count_frequency_rcr(str1@, x) > 1) == Seq::<
        u8,
    >::empty());
    let mut index = 0;
    while index < str1.len()
        invariant
            0 <= index <= str1.len(),
            str1@.take(index as int) =~= str1@.take(index as int).filter(
                |x: u8| count_frequency_rcr(str1@, x) <= 1,
            ),
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
