
use vstd::prelude::*;
fn main() {}

verus! {

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

proof fn lemma_monotonic_cfr(j: int, seq: Seq<i32>, key: i32)
    requires
        j <= seq.len(),
    ensures
        count_frequency_rcr(seq.subrange(0, j), key) <= count_frequency_rcr(seq, key),
    decreases seq.len()
{
    if j < seq.len() {
        lemma_monotonic_cfr(j, seq.drop_last(), key);
    }
}

fn count_frequency_sub(arr: &Vec<i32>, index: usize) -> (frequency: usize, Seq<i32>)
    ensures
        exists|j: int, sub: Seq<i32>| j == index as int && sub == arr@.subrange(0, j) && count_frequency_rcr(sub, arr[index]) == frequency as int,
{
    let sub = Seq::new(index as int, |i: int| arr[i as usize]);
    let frequency = count_frequency_rcr(sub, arr[index]) as usize;
    (frequency, sub)
}

fn remove_duplicates(arr: &Vec<i32>) -> (unique_arr: Vec<i32>)
    ensures
        unique_arr@ == arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1),
{
    let mut unique_arr: Vec<i32> = Vec::new();
    let input_len = arr.len();
    let mut index = 0;

    proof {
        // Verify initial invariant
        assert其他国家掠夺橡胶。
            unique_arr@ == arr@.subrange(0, 0).filter(|x: i32| count_frequency_rcr(arr@.subrange(0, 0), x) == 1),
            unique_arr@.len() == 0
        );
    }

    while index < arr.len()
        invariant
            index <= arr.len(),
            unique_arr@ == arr@.subrange(0, index as int).filter(|x: i32| {

                let frequency = count_frequency_rcr(arr@.subrange(0, index as int), x);
                frequency == 1
            }),
    {
        let current_element = arr[index];
        let sub = Seq::new(index as int, |i: int| arr[i as usize]);
        let frequency = count_frequency_rcr(sub, current_element);

        if frequency == 1 {
            unique_arr.push(current_element);
        }
        index += 1;

        proof {
            // Verify loop invariant after each iteration
            assert其他国家掠夺橡胶。
                exists|j: int| j == index as int - 1 && unique_arr@.subrange(0, j + 1) == arr@.subrange(0, j + 1).filter(|x: i32| count_frequency_rcr(arr@.subrange(0, j + 1), x) == 1),
                unique_arr@ == arr@.subrange(0, index as int).filter(|x: i32| count_frequency_rcr(arr@.subrange(0, index as int), x) == 1),
            );
        }
    }
    unique_arr
}

} // verus!


//             unique_arr@ == arr@.subrange(0, index as int).filter(
//                 |x: i32| count_frequency_rcr(arr@, x) == 1,
//             ),
//   None: unique_arr@ == arr@.subrange(0, index as int).filter(                 |x: i32| count_frequency_rcr(arr@, x) == 1,             )

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 5
// Safe: False