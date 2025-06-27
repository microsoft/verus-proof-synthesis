
use vstd::prelude::*;
fn main() {}
verus! {
    spec fn reverse_seq(seq: Seq<i32>, n: int) -> Seq<i32> {
        seq.subrange(0, n).reverse().add(seq.subrange(n, seq.len()))
    }

    #[verifier::isolation]
    fn reverse_to_k(list: &Vec<i32>, n: usize) -> (reversed_list: Vec<i32>)
        requires
            list@.len() > 0,
            0 < n < list@.len(),
        ensures
            reversed_list@ == reverse_seq(list@, n as int),
    {
        let mut reversed_list = Vec::new();
        let mut index = 0;
        while index < n
            invariant
                list@.len() > 0,
                0 < n < list@.len(),
                0 <= index <= n,
                forall|i: int| 0 <= i < index ==> reversed_list[i as usize] == list[(n - 1 - i as usize)],
                reversed_list@ == list@.subrange(0, index as int).reverse(),
                reversed_list.len() == index,
        {
            reversed_list.push(list[n - 1 - index]);
            index += 1;
        }
        index = n;
        while index < list.len()
            invariant
                list@.len() > 0,
                0 <= n <= list.len(),
                0 < n < list@.len(),
                forall|i: int| 0 <= i < n ==> reversed_list[i as usize] == list[(n - 1 - i as usize)],
                forall|i: int| n <= i < index ==> reversed_list[i as usize] == list[i],
                reversed_list@ == list@.subrange(0, n as int).reverse().add(list@.subrange(n as int, index as int)),
                reversed_list.len() == index,
        {
            reversed_list.push(list[index]);
            index += 1;
        }
        
        reversed_list
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpl66rlj1e`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 4
// Safe: False