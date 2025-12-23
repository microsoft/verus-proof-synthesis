
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_isolation(false)]
    fn remove_kth_element(list: &Vec<i32>, k: usize) -> (new_list: Vec<i32>)
        requires
            list.len() > 0,
            0 < k < list@.len(),
        ensures
            new_list@ == list@.subrange(0, k as int - 1).add(
                list@.subrange(k as int, list.len() as int),
            ),
    {
        let mut new_list = Vec::new();
        let mut index = 0;

        // Handling elements before the k-th element
        while index < k - 1
            invariant
                forall|i: int| 0 <= i < index ==> new_list@.index(i) == list@.index(i),
                index < k,
                new_list.len() == index,
                list.len() > 0,
                0 < k < list@.len(),
        {
            new_list.push(list[index]);
            index += 1;
        }

        // Handling elements starting from the k-th element
        let mut index = k;
        while index < list.len()
            invariant
                forall|i: int| 0 <= i < k - 1 ==> new_list@.index(i) == list@.index(i),
                forall|i: int| k <= i < index ==> new_list@.index(i - 1) == list@.index(i),
                index <= list.len(),
                new_list.len() == index - 1,
                list.len() > 0,
                0 < k < list@.len(),
        {
            new_list.push(list[index]);
            index += 1;
        }

        new_list
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp61vnqp1t`)
// 

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 2
// Safe: False