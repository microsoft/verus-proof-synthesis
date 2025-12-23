
use vstd::prelude::*;
fn main() {}
verus! {
/*
 This lemma is often useful to put right after a loop that has a loop invariant involving Seq::take(i), with i being the loop index.
 Example usage:
    while ( k < s.len() )
      invariant
          ...
          k <= s.len(),
          ...s@.take(k as int)...,
          ...
    {
       ...
       k = k + 1;
    }
	lemma_seq_take_all(s@);
*/
proof fn lemma_seq_take_all<T>(v: Seq<T>)
    ensures
        v == v.take(v.len() as int),
{
    assert(v =~= v.take(v.len() as int));
}


/*
 This lemma is often useful to put near the end of a loop body that has a loop invariant involving Seq::take(i), with i being the loop index.
 Example usage:
    while ( k < s.len() )
      invariant
          ...
          k <= s.len(),
          ...s@.take(k as int)...,
          ...
    {
       ...
       k = k + 1;
       proof{
        lemma_seq_take_ascend(s@, k as int);
       }
    }
*/
proof fn lemma_seq_take_ascend<T>(v: Seq<T>, i: int)
    requires
        0 < i <= v.len(),
    ensures
        v.take(i as int).drop_last() == v.take(i-1),
{
    assert(v.take(i as int).drop_last() =~= v.take(i-1));
}


/*
 This lemma is often useful to put right after a loop that has a loop invariant involving Seq::subrange(0, i), with i being the loop index.

 Example usage:
    while ( k < s.len() )
      invariant
          ...
          k <= s.len(),
          ...s@.subrange(0, k as int)...,
          ...
    {
       ...
       k = k + 1;
    }
    proof{
     	lemma_seq_subrange_all(s@);
    }
 */

proof fn lemma_seq_subrange_all<T>(v: Seq<T>)
    ensures
        v == v.subrange(0, v.len() as int),
{
    assert(v =~= v.subrange(0, v.len() as int));
}


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
            // Added assertion to prevent counter overflow.
            assert(counter < usize::MAX) by {
                // Ensure counter does not overflow
            };
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
                0 <= k < str1.len() ==> count_frequency_rcr(str1@, #[trigger] str1[k]) <= 1
        },
{
    reveal(Seq::filter);
    
    let mut index = 0;
    while index < str1.len()
        invariant
            index <= str1.len(),
            str1.len() == str1.len(),
            forall|k: int| 0 <= k < index ==> count_frequency_rcr(str1@, #[trigger] str1[k]) <= 1,
    {
        if count_frequency(&str1, str1[index]) > 1 {
            proof {
                if (index as int) <= str1@.len() {
                    lemma_seq_take_all(str1@); // Added invocation of the lemma function
                }
                assert(str1@.take(index as int) =~= str1@.take(index as int).filter(
                    |x: char| count_frequency_rcr(str1@, x) <= 1
                ));
                assert(count_frequency_rcr(str1@, str1[( index ) as int]) > 1);
            }
            return Some((index, str1[index]));
        }
        index += 1;
      proof {
            if index as int > 0 {
                lemma_seq_take_ascend(str1@, index as int);  // Added invocation of the lemma function (Fixed by AI)
            }
        }
    }
    
    proof {
        assert(forall|k: int| 0 <= k < str1.len() ==> count_frequency_rcr(str1@, #[trigger] str1[k]) <= 1);
        lemma_seq_subrange_all(str1@); // Added invocation of the suggested lemma function
    }
    
    None
}

} // verus!


//                 assert(str1@.take(index as int) =~= str1@.take(index as int).filter(
//                     |x: char| count_frequency_rcr(str1@, x) <= 1
//                 ));
//   assertion failed: str1@.take(index as int) =~= str1@.take(index as int).filter(                     |x: char| count_frequency_rcr(str1@, x) <= 1                 )

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: True