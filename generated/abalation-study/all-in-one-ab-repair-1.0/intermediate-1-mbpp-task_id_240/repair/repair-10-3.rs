
use vstd::prelude::*;
fn main() {}

verus! {
    spec fn subrange_equal<T>(a: Seq<T>, b: Seq<T>, start: int, len: int) -> bool {
        forall|i: int| 0 <= i < len ==> a[start + i] == b[i]
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
                first_end == first.len() - 1,
                second.len() == second.len(),
                index <= first_end,
                forall|i: int| 0 <= i < index ==> replaced_list[i] == first[i],
        {
            replaced_list.push(first[index]);
            index += 1;
        }

        index = 0;

        while index < second.len()
            invariant
                first.len() > 0,
                replaced_list.len() == first_end + index,
                first_end == first.len() - 1,
                second.len() == second.len(),
                forall|i: int| 0 <= i < index ==> replaced_list[first_end + i] == second[i],
                subrange_equal(first@, replaced_list@, 0, first_end), // Ensures the first part matches 
                index <= second.len(),
        {
            replaced_list.push(second[index]);
            index += 1;
        }

        replaced_list
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpe7mxjomj`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: True