
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

        // First loop to append the second part (rest of the list)
        while index < list.len()
            invariant
                list@.len() > 0,
                0 < n < list@.len(),
                n <= index <= list.len(),
                new_list@ == list@.subrange(n as int, index as int),
        {
            new_list.push(list[index]);
            index += 1;
        }

        let mut index = 0;

        // Second loop to append the first part (up to n)
        while index < n
            invariant
                list@.len() > 0,
                0 < n < list@.len(),
                0 <= index <= n,
                new_list@ == list@.subrange(n as int, list@.len() as int).add(Seq::from_vec(&new_list).subrange(0, new_list.len() as int)).add(list@.subrange(0, index as int)),  // Updated the invariant here
        {
            new_list.push(list[index]);
            index += 1;
        }

        proof {
            // Proving that the new list contains the expected elements
            assert(new_list@ == list@.subrange(n as int, list@.len() as int).add(list@.subrange(0, n as int)));
        }

        new_list
    }
}


// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1