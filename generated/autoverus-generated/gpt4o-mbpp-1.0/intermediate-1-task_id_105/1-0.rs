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
            index <= arr.len(),
            counter <= index,
            counter <= arr.len(),
            count_boolean(arr@.take(index as int)) == counter as int,
    {
        if arr[index] {
            counter += 1;
        }
        index += 1;
    }
    counter
}

} // verus!
// is safe: False
// Score: Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 2