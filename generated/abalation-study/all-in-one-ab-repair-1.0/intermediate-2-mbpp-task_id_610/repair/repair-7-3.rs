
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_isolation(false)]
    fn remove_kth_element(list: &Vec<i32>, k: usize) -> (new_list: Vec<i32>)
        requires
            list.len() > 0,
            0 <= k < list.len(),
        ensures
            new_list@ == list@.subrange(0, k as int).add(
                list@.subrange(k as int + 1, list.len() as int),
            ),
    {
        let mut new_list = Vec::new();
        let mut index = 0;
        
        // First loop: copy elements before k
        while index < k
            invariant
                forall|i: int| 0 <= i < index as int ==> new_list[i] == list[i],
                index <= k,
                new_list.len() == index,
                new_list@.len() == index as int,
                list.len() > 0,
                0 <= k < list.len(),
        {
            new_list.push(list[index]);
            index += 1;
        }
        
        // Second loop: copy elements after k
        let mut index = k + 1;
        while index < list.len()
            invariant  
                forall|i: int| 0 <= i < k ==> new_list[i as int] == list[i as int], 
                forall|i: int| k < i <= index as int ==> new_list[(i - 1) as int] == list[i as int], 
                index <= list.len(), new_list.len() == index - 1, 
                new_list@.len() == (index - 1) as int,
                list.len() > 0, 
                0 <= k < list.len() 
        {
            new_list.push(list[index]);
            index += 1;
        }

        new_list
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpr5n78zh6`)
// 

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 4
// Safe: False