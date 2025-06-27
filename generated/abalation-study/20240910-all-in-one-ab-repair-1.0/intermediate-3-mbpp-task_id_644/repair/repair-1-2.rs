
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_isolation]
    fn reverse_to_k(list: &Vec<i32>, n: usize) -> (reversed_list: Vec<i32>)
        requires
            list@.len() > 0,
            0 < n < list@.len(),
        ensures
            reversed_list@ == list@.subrange(0, n as int).reverse().add(
                list@.subrange(n as int, list.len() as int),
            ),
    {
        let mut reversed_list = Vec::new();
        let mut index = 0;
        while index < n
            invariant
                list@.len() > 0,
                0 < n < list@.len(),
                0 <= index <= n,
                forall|i: int| 0 <= i < index ==> reversed_list[i as usize] == list[(n - 1 - i as usize) as usize],
                forall|j: int| 0 <= j < list@.len() ==> (j < index ==> reversed_list[j as usize] == list[(n - 1 - j) as usize]),
                index <= n,
                reversed_list@.len() == index as int,
                list@.len() == list.len(),
        {
            reversed_list.push(list[(n - 1 - index) as usize]);
            index += 1;
        }
        
        while index < list.len()
            invariant
                list@.len() > 0,
                0 < n < list@.len(),
                0 <= n < list.len(),
                n <= index <= list.len(),
                forall|i: int| 0 <= i < n ==> reversed_list[i as usize] == list[(n - 1 - i as usize) as usize],
                forall|j: int| 0 <= j < n ==> reversed_list[j as usize] == list[(n - 1 - j) as usize],
                forall|j: int| 0 <= j < list@.len() ==> ((n as int <= j < index as int) ==> reversed_list[j as usize] == list[j as usize]),
                index <= list.len(),
                reversed_list@.len() == index as int,
                list@.len() == list.len(),
        {
            reversed_list.push(list[index]);
            index += 1;
        }
        reversed_list
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpp9eww2mz`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 10
// Safe: False