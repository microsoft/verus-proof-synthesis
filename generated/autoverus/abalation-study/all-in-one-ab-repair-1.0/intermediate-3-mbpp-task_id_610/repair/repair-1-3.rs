
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_isolation(false)]
    fn remove_kth_element(list: &Vec<i32>, k: usize) -> (new_list: Vec<i32>)
        requires
            list.len() > 0,
            0 < k && k < list@.len(),
        ensures
            new_list@ == list@.subrange(0, k - 1 as int).add(
                list@.subrange(k as int, list.len() as int)
            ),
    {
        let mut new_list = Vec::new();
        let mut index = 0;
        while index < k
            invariant
                forall|i: int| 0 <= i < index ==> new_list[i] == list[i],
                index <= k,
                index <= k,
                new_list.len() == index,
                new_list@.len() == index,
                list.len() > 0,
                0 < k,
                k < list@.len(),
                list.len() == list.len(),
        {
            proof {
                assert(index < k);
            }
            new_list.push(list[index]);
            index += 1;
        }
        let mut index = k;
        while index < list.len()
            invariant
                forall|i: int| 0 <= i < k ==> new_list[i] == list[i],
                forall|i: int| k <= i < index ==> new_list@.index(i - 1) == list.index(i),
                index <= list.len(),
                index >= k,
                new_list.len() == index - 1,
                new_list@.len() == (index - 1) as int, // Using as int cast to resolve type
                list.len() > 0,
                0 < k,
                k < list@.len(),
                list.len() == list.len(),
        {
            proof {
                assert(index < list.len());
            }
            new_list.push(list[index]);
            index += 1;
        }
        proof {
            assert(new_list@ == list@.subrange(0, k - 1 as int).add(
                list@.subrange(k as int, list.len() as int)
            ));
        }
        new_list
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp_5av86b8`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False