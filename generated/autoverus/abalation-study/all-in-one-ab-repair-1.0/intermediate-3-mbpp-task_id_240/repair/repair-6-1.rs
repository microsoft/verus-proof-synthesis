
use vstd::prelude::*;
fn main() {}

verus! {
    fn replace_last_element(first: &Vec<i32>, second: &Vec<i32>) -> (replaced_list: Vec<i32>)
        requires
            first.len() > 0,
        ensures
            replaced_list@ == first@.subrange(0, first.len() - 1).add(second@),
    {
        let mut replaced_list = Vec::new();
        let first_end = first.len() - 1;
        let mut index = 0;

        // Loop to copy elements from first to replaced_list up to first_end
        while index < first_end
            invariant
                first.len() > 0,
                index <= first_end,
                replaced_list.len() == index,
                forall|i: int| 0 <= i < index ==> replaced_list@[i] == first@[i],
        {
            replaced_list.push(first[index]);
            index += 1;
        }

        index = 0;

        // Loop to copy all elements from second to replaced_list
        while index < second.len()
            invariant
                first.len() > 0,
                index <= second.len(),
                replaced_list.len() == first_end + index,
                forall|i: int| 0 <= i < first_end ==> replaced_list@[i] == first@[i],
                forall|k: int| 0 <= k < index ==> replaced_list@[first_end + k] == second@[k],
        {
            replaced_list.push(second[index]);
            index += 1;
        }

        replaced_list
    }

    proof fn test_replace_last_element() {
        let first = vec![1, 2, 3];
        let second = vec![4, 5, 6];
        let replaced_list = replace_last_element(&first, &second);

        let expected_list = vec![1, 2, 4, 5, 6];
        assert(replaced_list@ == expected_list@);

        let first = vec![7];
        let second = vec![8, 9];
        let replaced_list = replace_last_element(&first, &second);

        let expected_list = vec![8, 9];
        assert(replaced_list@ == expected_list@);
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpiwuir0ns`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: True