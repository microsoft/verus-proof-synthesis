
use vstd::prelude::*;
fn main() {}

verus! {
    spec fn subrange<A>(a: Seq<A>, start: int, end: int) -> Seq<A> {
        Seq::new(end - start, |i| a[i + start])
    }

    #[verifier::loop_isolation(false)]
    fn split_and_append(list: &Vec<i32>, n: usize) -> (new_list: Vec<i32>)
        requires
            list@.len() > 0,
            0 < n < list@.len(),
        ensures
            new_list@ == subrange(list@, n as int, list@.len() as int).add(subrange(list@, 0, n as int)),
    {
        let mut new_list: Vec<i32> = Vec::new();
        let mut index = n;
        
        while index < list.len()
            invariant
                0 < n < list@.len(),
                list@.len() > 0,
                n <= index <= list.len(),
                #[trigger] new_list@ == subrange(list@, n as int, index as int),
                list@.len() == list.len(),
        {
            new_list.push(list[index]);
            index += 1;
        }

        let mut index2 = 0; // Changed variable name to avoid shadowing
        
        while index2 < n
            invariant
                0 < n < list@.len(),
                0 <= index2 <= n,
                list@.len() > 0,
                #[trigger] new_list@ == subrange(list@, n as int, list@.len() as int).add(
                    subrange(list@, 0, index2 as int),
                ),
                list@.len() == list.len(),
        {
            new_list.push(list[index2]);
            index2 += 1;
        }
        
        new_list // returns new_list
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpcp2_hfzs`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False