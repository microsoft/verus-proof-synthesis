use vstd::prelude::*;

fn main() {}

verus! {

spec fn count_boolean(seq: Seq<bool>) -> int
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_boolean(seq.drop_last()) + if (seq.last()) {
            1 as int
        } else {
            0 as int
        }
    }
}

fn count_true(arr: &Vec<bool>) -> (count: u64)
    ensures
        0 <= count <= arr.len(),
        count_boolean(arr@) == count,
{
    let mut index = 0;
    let mut counter = 0;

    while index < arr.len()
        invariant
            0 <= index <= arr.len(),  // bounds for index
            0 <= counter <= index as u64,  // bounds for counter
            counter as int == count_boolean(arr@.take(index as int)),  // correctness of the counter
    {
        if (arr[index]) {
            counter += 1;
        }
        index += 1;
    }
    counter
}

} // verus!

// Score: (1, 2)
// Safe: True