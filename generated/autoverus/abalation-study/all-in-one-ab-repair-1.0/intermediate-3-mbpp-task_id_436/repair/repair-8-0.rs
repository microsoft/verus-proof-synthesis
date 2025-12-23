
use vstd::prelude::*;

fn main() {}

verus! {

fn find_negative_numbers(arr: &Vec<i32>) -> (negative_list: Vec<i32>)
    ensures
        // Ensures the resulting negative_list satisfies the filter condition
        negative_list@ == arr@.filter(|x: i32| x < 0),
{
    proof {
        // Reveal the filter specifications to the verifier
        reveal(Seq::filter);
        reveal_with_fuel(Seq::subrange, 10);  // Give the verifier more fuel to process subrange calls
    }

    let mut negative_list: Vec<i32> = Vec::new();
    let mut index = 0;

    // Initial assertion about the empty negative_list
    assert(negative_list@ == arr@.subrange(0, index as int).filter(|x: i32| x < 0));

    while index < arr.len()
        invariant
            // Invariant to maintain properties during the loop
            0 <= index <= arr.len(),
            negative_list@ == arr@.subrange(0, index as int).filter(|x: i32| x < 0),
            arr.len() == arr.len(),
    {
        if arr[index] < 0 {
            negative_list.push(arr[index]);
            proof {
                // Additional proof for the post-condition after pushing a negative number
                assert(negative_list@ == arr@.subrange(0, index as int + 1).filter(|x: i32| x < 0));
            }
        } else {
            proof {
                // Proof for the case when the current element is non-negative
                assert(negative_list@ == arr@.subrange(0, index as int + 1).filter(|x: i32| x < 0));
            }
        }
        
        index += 1;

        proof {
            // Additional in-loop assertions or lemma usage if needed
        }
    }

    proof {
        // Verify the final condition
        lemma_seq_subrange_all(arr@);
    }

    // Return the constructed list of negative numbers
    negative_list
}

// Lemma to prove properties about sequence subranges
proof fn lemma_seq_subrange_ascend<T>(v: Seq<T>, i: int, j: int)
    requires
        0 <= i < j <= v.len(),
    ensures
        v.subrange(i as int, j as int).drop_last() == v.subrange(i as int, j - 1),
{
    assert(v.subrange(i as int, j as int).drop_last() =~= v.subrange(i as int, j - 1));
}

// Lemma to prove that a sequence is equivalent to its full subrange
proof fn lemma_seq_subrange_all<T>(v: Seq<T>)
    ensures
        v == v.subrange(0, v.len() as int),
{
    assert(v =~= v.subrange(0, v.len() as int));
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpjuvhd2zk`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False