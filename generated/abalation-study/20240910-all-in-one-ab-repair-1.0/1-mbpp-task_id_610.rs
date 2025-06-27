
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_isolation(false)]
    fn remove_kth_element(list: &Vec<i32>, k: usize) -> (new_list: Vec<i32>)
        requires
            list.len() > 0,
            0 < k < list@.len(),
        ensures
            new_list@ == list@.subrange(0, k - 1 as int).add(
                list@.subrange(k as int, list.len() as int),
            ),
    {
        let mut new_list = Vec::new();
        let mut index = 0;

        // Loop to copy elements from 0 to k-1
        while index < (k - 1)
            invariant
                index <= k - 1,
                forall|i: int| 0 <= i < index ==> new_list[i] == list[i],
                new_list.len() == index,
                list.len() > 0,
                0 < k < list@.len(),
        {
            new_list.push(list[index]);
            index += 1;
        }

        // Proof to ensure the state of the list before entering the second loop
        proof {
            assert(forall|i: int| 0 <= i < index ==> new_list[i] == list[i]);
        }

        // Loop to copy elements from k to the end
        index = k;
        while index < list.len()
            invariant
                index >= k,
                index <= list.len(),
                forall|i: int| 0 <= i < (k - 1) ==> new_list[i] == list[i],
                forall|i: int| k <= i < index ==> new_list[i - 1] == list[i],
                new_list.len() == index - 1,
                list.len() > 0,
                0 < k < list@.len(),
        {
            new_list.push(list[index]);
            index += 1;
        }

        // Proof to ensure the state of the final list
        proof {
            assert(new_list@ == list@.subrange(0, k - 1 as int).add(list@.subrange(k as int, list.len() as int)));
        }

        new_list
    }
}

// Score: (1, 0)
// Safe: False