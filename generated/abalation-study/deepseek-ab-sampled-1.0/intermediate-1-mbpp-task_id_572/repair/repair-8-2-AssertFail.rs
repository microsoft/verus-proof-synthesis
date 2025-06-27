
use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]

extern_spec!{
spec fn count_frequency_rcr(seq: Seq<i32>, key: i32) -> int
}

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

extern_spec!{
spec fn count_frequency(arr: &Vec<i32>, key: i32) -> (frequency: usize);
}

extern_spec!{
spec fn remove_duplicates(arr: &Vec<i32>) -> (unique_arr: Vec<i32>);
}

proof fn lemma_count_frequency_correct(arr: &Vec<i32>, key: i32)
    ensures
        count_frequency(arr, key) == count_frequency_rcr(arr@, key) as usize,
{
    let mut index = 0;
    let mut counter = 0;
    let n = arr.len();

    while index < n {
        invariant [
            counter == arr.subseq(0..index).filter(|x| x == key).len(),
        ];
        if arr[index] == key {
            counter += 1;
        }
        index += 1;
    }
    assert前几年 the counter matches the recursive count_frequency_rcr
    assert(count_frequency(arr, key) == count_frequency_rcr(arr@, key) as usize);
}

proof fn lemma_unique_filter_correct<'a>(arr: &Vec<i32>)
    ensures
        arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1) == 
        arr@.filter(|x: i32| count_frequency(arr, x) == 1),
{
    assert(forall |x: i32|
        #[trigger] arr@.contains(x)
        ==> 
        count_frequency(arr, x) == count_frequency_rcr(arr@, x) as usize
    ) by {
        lemma_count_frequency_correct(arr, x);
    }

    assert(arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1) == 
        arr@.filter(|x: i32| count_frequency(arr, x) == 1));
}

fn count_frequency(arr: &Vec<i32>, key: i32) -> (frequency: usize)
    ensures
        count_frequency_rcr(arr@, key) == frequency,
{
    let mut index = 0;
    let mut counter = 0;
    let n = arr.len();

    while index < n
        invariant
            0 <= counter,
            index <= n,
            counter <= index,
    {
        if arr[index] == key {
            counter += 1;
        }
        index += 1;
    }
    counter
}

fn remove_duplicates(arr: &Vec<i32>) -> (unique_arr: Vec<i32>)
    ensures
        unique_arr@ == arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1),
{
    let mut unique_arr: Vec<i32> = Vec::new();
    let n = arr.len();
    let mut index = 0;

    while index < n
        invariant
            0 <= index <= n,
            unique_arr.len() <= index,
            forall |i: int| 0 <= i < unique_arr.len()
                ==> count_frequency_rcr(arr@, unique_arr[i]) == 1,
    {
        if count_frequency(arr, arr[index]) == 1 {
            unique_arr.push(arr[index]);
        }
        index += 1;
    }
    proof {
        assert(unique_arr@ == arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1));
    }
    unique_arr
}

} // verus!


//         assert(unique_arr@ == arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1));
//   assertion failed: unique_arr@ == arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1)

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False