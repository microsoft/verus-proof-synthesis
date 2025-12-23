
use vstd::prelude::*;

fn main() {}

verus! {

    open spec fn count_frequency_rcr(seq: Seq<i32>, key: i32) -> int
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

    proof fn lemma_seq_drop_last_len<T>(seq: Seq<T>)
        requires
            seq.len() > 0,
        ensures
            seq.drop_last().len() == seq.len() - 1,
        {
            assert(seq.drop_last().len() == seq.len() - 1);
        }

    proof fn lemma_seq_last_filter_eq<T, P>(seq: Seq<T>, predicate: P)
        requires
            seq.len() > 0,
        ensures
            seq.filter(|x: T| predicate(x)).last() == seq.last(),
        {
            assert(seq.filter(|x: T| predicate(x)).last() == seq.last());
        }

    proof fn lemma_count_frequency_eq<T>(arr: Seq<T>, key: T)
        ensures
            count_frequency_rcr(arr, key) == arr.filter(|x: T| x == key).len() as int,
        {
            assert(count_frequency_rcr(arr, key) == arr.filter(|x: T| x == key).len() as int);
        }

    pub fn count_frequency(arr: &Vec<i32>, key: i32) -> (frequency: usize)
        ensures
            count_frequency_rcr(arr@, key) == frequency,
    {
        let mut index = 0;
        let mut counter = 0;
        while index < arr.len()
            invariant
                0 <= index <= arr.len(),
                counter == arr.subrange(0, index as int).filter(|x: i32| x == key).len(),
        {
            if (arr[index] == key) {
                counter += 1;
            }
            index += 1;
        }
        counter
    }

    pub fn remove_duplicates(arr: &Vec<i32>) -> (unique_arr: Vec<i32>)
        ensures
            unique_arr@ == arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1),
    {
        let mut unique_arr: Vec<i32> = Vec::new();
        let mut index = 0;
        while index < arr.len()
            invariant
                0 <= index <= arr.len(),
                forall |k:int| 0 <= k < index ==> count_frequency_rcr(arr@, arr[k]) == 1,
                unique_arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1) == arr.subrange(0, index)
        {
            if count_frequency(&arr, arr[index]) == 1 {
                unique_arr.push(arr[index]);
            }
            index += 1;

            proof {
                lemma_seq_drop_last_len(arr@);
                lemma_seq_last_filter_eq(arr@, |x: i32| count_frequency_rcr(arr@, x) == 1);
                lemma_count_frequency_eq(arr@, arr[index]);
            }
        }
        unique_arr
    }

} // verus!

// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 7