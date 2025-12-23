
use vstd::prelude::*;
fn main() {}
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
            counter == count_frequency_rcr(arr@.subrange(0, index as int), key),
            index <= arr.len(),
            arr.len() == arr.len(),
    {
        if (arr[index] == key) {
            counter += 1;
        }
        index += 1;
    }
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
                0 <= k < str1.len() ==> count_frequency_rcr(str1@, # [trigger] str1[k]) <= 1
        },
{
    let mut index = 0;
    while index < str1.len()
        invariant
            forall|k: int| 0 <= k < index ==> count_frequency_rcr(str1@, # [trigger] str1[k]) <= 1,
            index <= str1.len(),
            str1.len() == str1.len(),
    {
        if count_frequency(&str1, str1[index]) > 1 {
            return Some((index, str1[index]));
        }
        index += 1;
    }
    None
}

} // verus!
