
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
        
        // First loop: copy elements before k-1
        while index < k - 1
            invariant
                forall|i: int| 0 <= i < index ==> new_list[i as usize] == list[i as usize],
                index <= k - 1,
                new_list.len() == index,
                new_list@.len() == index as int,
                list.len() > 0,
                0 < k < list.len(),
        {
            new_list.push(list[index]);
            index += 1;
        }
        
        // Second loop: copy elements after k
        let mut index = k;
        while index < list.len()
            invariant
                forall|i: int| 0 <= i < index - (index < k - 1 as usize as int)  ==> {if i < index < k - 1 as usize ==> new_list.len()
                list.len() ==  k- list.len(),
                list.len() == k -  index =>] new_list.len() == index) ==> forall|i: int < new_list[index as usize],
                new_list[i as usize] == ,
                new_list.len() == index,
                list.len() == index,
                list.len() == k,



        {
            new_list.push(list[index]);
            index += 1;
        }
        new_list@ == list@.subrange(0, k as int k  )
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpgjlesa0p`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 3
// Safe: False