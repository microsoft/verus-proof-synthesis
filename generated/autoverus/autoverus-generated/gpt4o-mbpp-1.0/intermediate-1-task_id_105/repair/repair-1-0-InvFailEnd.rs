use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

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
            0 <= counter <= index,
            0 <= counter,
            0 <= index <= arr.len(),
            count_boolean(arr@.subrange(0, index as int)) == counter as int,
            index <= arr.len(),
            arr.len() == arr.len(), // Loop Invariant specifying length of arr
            // Adding a loop invariant to cover all elements since `arr` is not modified in the loop.
            forall |k: int| 0 <= k < arr.len() ==> arr@[k] == arr@[k], // added based on observation that arr is never modified within the loop
    {
        if (arr[index]) {
            counter += 1;
        }
        index += 1;
        
        proof {
            assert(count_boolean(arr@.subrange(0, index as int)) == counter as int);
        } // Added by AI
    }
    counter
}

} // verus!

//             count_boolean(arr@.subrange(0, index as int)) == counter as int,
//   None: count_boolean(arr@.subrange(0, index as int)) == counter as int

// Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 2
// Safe: True