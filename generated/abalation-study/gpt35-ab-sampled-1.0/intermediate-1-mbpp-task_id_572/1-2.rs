
use vstd::prelude::*;

fn main() {}

verus! {

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

    proof fn lemma_seq_filter_count<T>(seq: Seq<T>, pred: &Func<T, bool>, x: T)
        requires
            pred(x) == true,
        ensures
            count_frequency_rcr(seq@, x) == 1,
    {
        assert(count_frequency_rcr(seq@, x) == 1);
    }

    fn count_frequency(arr: &Vec<i32>, key: i32) -> (frequency: usize)
        ensures
            count_frequency_rcr(arr@, key) == frequency,
    {
        let mut index = 0;
        let mut counter = 0;
        while index < arr.len()
            invariant
                index <= arr.len(),
                forall |j: int| 0 <= j < index ==> count_frequency_rcr(arr@, arr[j]) == counter,
        {
            if (arr[index] == key) {
                counter += 1;
            }
            index += 1;

            proof {
                lemma_seq_filter_count(arr@, &Func::eq(key), key);
            }
        }
        counter
    }

    fn remove_duplicates(arr: &Vec<i32>) -> (unique_arr: Vec<i32>)
        ensures
            unique_arr@ == arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1),
    {
        let mut unique_arr: Vec<i32> = Vec::new();
        let mut index = 0;
        while index < arr.len()
            invariant
                index <= arr.len(),
                unique_arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1) == unique_arr,
        {
            if count_frequency(&arr, arr[index]) == 1 {
                unique_arr.push(arr[index]);
            }
            index += 1;
        }
        unique_arr
    }

} // verus!

// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2