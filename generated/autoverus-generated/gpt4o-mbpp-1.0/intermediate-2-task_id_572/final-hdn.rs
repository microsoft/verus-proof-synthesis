
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
    lemma_seq_take_all(s@);
    }
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

#[verifier::loop_isolation(false)]
pub open spec fn count_frequency_rcr(seq: Seq<i32>, key: i32) -> int
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

fn count_frequency(arr: &Vec<i32>, key: i32) -> (frequency: usize)
    ensures
        count_frequency_rcr(arr@, key) == frequency,
{
    let mut index = 0;
    let mut counter = 0;
    while index < arr.len()
        invariant
            arr.len() <= arr@.len(),
            index <= arr.len(),
            forall |k: int| 0 <= k < arr.len() ==> arr[k] == arr[k], // No modification of array in loop
    {
        if (arr[index] == key) {
                // ensure that counter + 1 will not overflow
            };
            counter += 1;
        }

        assert(index < arr.len()) by {
            // ensure that index + 1 will not overflow
        };
        index += 1;
    }
    counter
}

fn remove_duplicates(arr: &Vec<i32>) -> (unique_arr: Vec<i32>)
    ensures
        unique_arr@ == arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1),
{
    proof {
        reveal(Seq::filter); // Adding reveal at the beginning of the function
    }

    let mut unique_arr: Vec<i32> = Vec::new();
    let input_len = arr.len();
    let mut index = 0;

    proof {
        assert(unique_arr@ == arr@.take(index as int).filter(|x: i32| count_frequency_rcr(arr@, x) == 1));
    }

    while index < arr.len()
        invariant
            index <= arr.len(),
            unique_arr@ == arr@.take(index as int).filter(
                |x: i32| count_frequency_rcr(arr@, x) == 1,
            ),
            forall |k: int| 0 <= k < arr.len() ==> arr[k] == arr[k], // No modification of array in loop
    {
        if count_frequency(&arr, arr[index]) == 1 {
            unique_arr.push(arr[index]);
        }

        assert(index < arr.len()) by {
            // ensure that index + 1 will not overflow
        };
        index += 1;
        
        proof {
            if index > 0 {
                lemma_seq_take_ascend(arr@, index as int);
            }
        }
    }

    proof {
        lemma_seq_take_all(arr@);
        assert(unique_arr@ == arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1)); // assertion fixed using lemma_seq_take_all
    }
    unique_arr
}
} // verus!


// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1