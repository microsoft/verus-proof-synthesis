
use vstd::prelude::*;
fn main() {}

verus! {
    fn replace_last_element(first: &Vec<i32>, second: &Vec<i32>) -> (replaced_list: Vec<i32>)
        requires
            first.len() > 0,
        ensures
            replaced_list@ == first@.subrange(0, first.len() - 1).add(second@),
    {
        let mut replaced_list = Vec::new();
        let first_end = first.len() - 1;
        let mut index = 0;

        // Loop to copy elements from first to replaced_list up to first_end
        while index < first_end
            invariant
                first.len() > 0,
                index <= first_end,
                replaced_list.len() == index,
                forall|i: int| 0 <= i < index ==> replaced_list@[i] == first@[i],
        {
            replaced_list.push(first[index]);
            index += 1;
        }

        index = 0;

        // Loop to copy all elements from second to replaced_list
        while index < second.len()
            invariant
                first.len() > 0,
                index <= second.len(),
                replaced_list.len() == first_end + index,
                forall|i: int| 0 <= i < first_end ==> replaced_list@[i] == first@[i],
                forall|k: int| 0 <= k < index ==> replaced_list@[first_end + k] == second@[k],
        {
            replaced_list.push(second[index]);
            index += 1;
        }

        proof {
            // Reconstruct the sequence and assert our final list is correct
            let replaced_seq = first@.subrange(0, first_end as int).add(second@); 
            assert(replaced_list@ == replaced_seq) by {
                // Check the sequence parts manually
                assert(replaced_list.len() == first_end + second.len()) by {
                    assert(replaced_list.len() == first_end + index);
                }
                for i in 0..first_end {
                    assert(replaced_list@[i] == first@[i]);
                }
                for k in 0..second.len() {
                    assert(replaced_list@[first_end + k] == second@[k]);
                }
                // Conclude the total assertion
                assert(replaced_list@ == replaced_seq);
            };
        }

        replaced_list
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp6gca73rq`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 3
// Safe: True