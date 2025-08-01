
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_isolation(false)]
    fn split_and_append(list: &Vec<i32>, n: usize) -> (new_list: Vec<i32>)
        requires
            list@.len() > 0,
            0 < n < list@.len(),
        ensures
            new_list@ == list@.subrange(n as int, list@.len() as int).add(list@.subrange(0, n as int)),
    {
        let mut new_list = Vec::new();
        let mut index = n;
        while index < list.len()
            invariant
                0 < n < list@.len(), // n is between 0 and the length of the list, exclusive
                list@.len() > 0, // the length of the list should be greater than 0
                n <= index <= list.len(), // index is between n and list length
                new_list@.len() == (index - n) as int, // Partial new_list contains correct number of elements
                forall|i: int| 0 <= i < new_list@.len() ==> new_list@[i] == list@[(n as int + i)] // Elements match
        {
            new_list.push(list[index]);
            index += 1;
        }
        
        let mut index = 0;
        while index < n
            invariant
                0 < n < list@.len(), // n is between 0 and the length of the list, exclusive
                0 <= index <= n, // index is between 0 and n, inclusive
                list@.len() > 0, // the length of the list should be greater than 0
                new_list@.len() == (list.len() - n + index) as int, // new_list contains correct number of elements
                forall|i: int| 0 <= i < (list.len() - n) as int ==> new_list@[i] == list@[(n as int + i)], // Elements from n to end
                forall|i: int| 0 <= i < index as int ==> new_list@[(list.len() - n) as int + i] == list@[i] // Additional elements from 0 to index
        {
            new_list.push(list[index]);
            index += 1;
        }
        
        new_list
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp3vty43tc`)
// 

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1
// Safe: True