
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_isolation(false)]
    spec fn is_subrange_with_addition<T>(a: Seq<T>, b: Seq<T>, c: Seq<T>, n: nat) -> bool {
        a.len() > n && a.subrange(0, n).add(c) =~= b && forall|i: nat| 0 <= i < n ==> a[i] == b[i]
    }

    fn replace_last_element(first: &Vec<i32>, second: &Vec<i32>) -> (replaced_list: Vec<i32>)
        requires
            first.len() > 0,
        ensures
            replaced_list@ == first@.subrange(0, first.len() - 1).add(second@),
    {
        let mut replaced_list = Vec::new();
        let first_end = first.len() - 1;
        let mut index = 0;
        while index < first_end
            invariant
                first.len() > 0,
                replaced_list.len() == index,
                first.len() == first.len(),
                second.len() == second.len(),
                forall|i: int| 0 <= i < index ==> replaced_list@[i as nat] == first@[i as nat],
                index <= first_end,
        {
            replaced_list.push(first[index]);
            index += 1;
        }

        index = 0;
        while index < second.len()
            invariant
                first.len() > 0,
                replaced_list.len() == first_end + index,
                first.len() == first.len(),
                second.len() == second.len(),
                forall|i: int| 0 <= i < index ==> replaced_list@[first_end + i as nat] == second@[i as nat],
                index <= second.len(),
        {
            replaced_list.push(second[index]);
            index += 1;
        }
        replaced_list
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpzlzroahu`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 6
// Safe: True