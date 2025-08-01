
use vstd::prelude::*;
fn main() {}

verus! {
    
    #[verifier(loop_isolation)]
    fn remove_kth_element(list: &Vec<i32>, k: usize) -> (new_list: Vec<i32>)
        requires
            list.len() > 0,
            0 <= k < list@.len(),
        ensures
            new_list@ == list@.subrange(0, k as int).add(list@.subrange((k + 1) as int, list.len() as int)),
    {
        let mut new_list = Vec::new();
        let mut index = 0;
        
        while index < k
            invariant
                forall |i: int| 0 <= i < index ==> new_list@[i] == list@[i],
                new_list.len() == index,
                index <= k,
                list.len() > 0,
                0 <= k < list.len(),
        {
            new_list.push(list[index]);
            index += 1;
        }
        
        index = k + 1;
        
        while index < list.len()
            invariant
                forall |i: int| 0 <= i < k ==> new_list@[i] == list@[i],
                forall |i: int| k < i + 1 <= index ==> new_list@[i] == list@[i + 1],
                new_list.len() == index - 1,
                list.len() > 0,
                0 <= k < list.len(),
        {
            new_list.push(list[index]);
            index += 1;
        }
        
        new_list
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpoib9lzg_`)
// 

// Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 4
// Safe: False