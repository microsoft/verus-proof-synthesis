
use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]

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

// Proof function to demonstrate bound
proof fn lemma_frequency_bound(seq: Seq<char>, key: char)
    ensures
        count_frequency_rcr(seq, key) as usize <= seq.len(),
{
    // Induction on the length of the sequence
    if seq.len() == 0 {
        assert(count_frequency_rcr(seq, key) == 0);
    } else {
        // Recursive call
        lemma_frequency_bound(seq.drop_last(), key);
        assert(count_frequency_rcr(seq, key) <= (seq.len() as int));
    }
}

fn count_frequency(arr: &Vec<char>, key: char) -> (frequency: usize)
    ensures
        count_frequency_rcr(arr@, key) == frequency,
{
    let mut index = 0;
    let mut counter = 0;
    lemma_frequency_bound(arr@, key); // call proof function to setup bounds
    while index < arr.len()
        invariant
            counter as int == count_frequency_rcr(arr@.take(index as int), key),
            index <= arr.len(),
            // The array `arr` is not modified in this loop
            forall|k: int| 0 <= k < arr.len() ==> arr[k] == arr[k],
            index < arr.len(), // Reiteration of invariant
        decreases arr.len() - index,
    {
        if (arr[index] == key) {
            assert(counter < usize::MAX); // Ensure we don't overflow
            assert(counter + 1 as usize <= arr.len());
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
            index <= str1.len(),
            // The array `str1` is not modified in this loop
            forall|k: int| 0 <= k < str1.len() ==> str1[k] == str1[k],
            true,
            index < str1.len(), // Reiteration of invariant
        decreases str1.len() - index,
    {
        if count_frequency(&str1, str1[index]) > 1 {
            return Some((index, str1[index]));
        }
        index += 1;
    }
    None
}

} // verus!


//             counter += 1;
//   None: counter += 1

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False