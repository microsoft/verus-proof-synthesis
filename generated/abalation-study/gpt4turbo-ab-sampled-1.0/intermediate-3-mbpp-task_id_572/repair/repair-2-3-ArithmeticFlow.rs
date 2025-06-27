
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

fn count_frequency(arr: &Vec<i32>, key: i32) -> (frequency: usize)
    ensures
        count_frequency_rcr(arr@, key) == frequency,
{
    let mut index = 0;
    let mut counter = 0;
    while index < arr.len()
        invariant
            index <= arr.len(),
            count_frequency_rcr(arr@.subrange(0, index as int), key) == counter,
    {
        if (arr[index] == key) {
	    assert(counter + 1 <= arr.len()) by {
                // Justification for why the counter + 1 will not overflow:
		// The counter is incremented only when arr[index] == key,
		// implying that each increment of counter correlates directly
		// to a unique index within arr. Therefore, the maximum value
		// of counter must be bounded by arr.len().
	    };
            counter += 1;
        }
        index += 1;
    }
    counter
}
}


//             counter += 1;
//   None: counter += 1

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False