
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_isolation(false)]
    fn remove_kth_element(list: &Vec<i32>, k: usize) -> (new_list: Vec<i32>)
        requires
            list.len() > 0,
            0 < k < list@.len(),
        ensures
            new_list@ == list@.subrange(0, k as int).add(
                list@.subrange(k as int + 1, list.len() as int),
            ),
    {
        let mut new_list = Vec::new();
        let mut index = 0;
        // Loop to copy elements from 0 to k-1
        while index < k
            invariant
                0 <= index <= k,
                forall|i: int| 0 <= i < index ==> new_list[i as usize] == list[i as usize],
                new_list.len() == index,
                list.len() > 0,
                0 < k < list@.len(),
        {
            proof {
                assert(0 <= index < k);
                // assert(0 <= index < list.len() && 0 <= list.len() && new_list.len() == index);
            }
            new_list.push(list[index]);
            index += 1;
        }
        // Loop to copy elements from k to the end
        let mut index = k + 1;  // start after the k-th element
        while index < list.len()
            invariant
                k < index <= list.len(),
                forall|i: int| 0 <= i < k ==> new_list[i as usize] == list[i as usize],
                forall|i: int| k < i < index ==> new_list[i as usize - 1] == list[i as usize],
                new_list.len() == index - 1 - 1,
                list.len() > 0,
                0 < k < list@.len(),
        {
            proof {
                assert(k < index < list.len());
                // assert(0 <= index < list.len() && 0 <= list.len() && new_list.len() == index - 1);
            }
            new_list.push(list[index]);
            index += 1;
        }
        new_list
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpddgs61b3`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 5
// Safe: False