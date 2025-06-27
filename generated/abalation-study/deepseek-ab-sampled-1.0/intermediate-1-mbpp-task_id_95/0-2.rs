

use vstd::prelude::*;

fn main() {}

verus! {

    fn smallest_list_length(list: &Vec<Vec<i32>>) -> (min: usize)
        requires
            list.len() > 0,
        ensures
            min >= 0,
            forall|i: int| 0 <= i < list.len() ==> min <= #[trigger] list[i].len(),
            exists|i: int| 0 <= i < list.len() && min == #[trigger] list[i].len(),
    {
        let mut min = list[0].len();
        let mut index = 1;
        
        while index < list.len()
            invariant
                index <= list.len(),
                min >= 0,
                forall|i: int| 0 <= i < index ==> list[i].len() >= min,
        {
            if list[index].len() < min {
                min = list[index].len();
            }
            index += 1;
        }

        min
    }

}
} // verus!
// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1