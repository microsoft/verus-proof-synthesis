
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_invariant_as_ext(false)]
    fn min_second_value_first(arr: &Vec<Vec<i32>>) -> (first_of_min_second: i32)
        requires
            arr.len() > 0,
            forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() >= 2,
        ensures
            exists|i: int|
                0 <= i < arr.len() && first_of_min_second == #[trigger] arr[i][0] && (forall|j: int|
                    0 <= j < arr.len() ==> (arr[i][1] <= #[trigger] arr[j][1])),
    {
        let mut min_second_index = 0;
        let mut index = 0;
        while index < arr.len()
            invariant
                0 <= index <= arr.len(),
                0 <= min_second_index < arr.len(),
                forall|i: int| 0 <= i < index ==> arr[min_second_index as int][1] <= arr[i][1],
                arr.len() > 0,
                forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() >= 2,
        {
            if arr[index][1] < arr[min_second_index][1] {
                min_second_index = index;
            }
            index += 1;
        }
        
        proof {
            assert(arr.len() > 0);
            assert(0 <= min_second_index < arr.len());
            assert(0 <= index <= arr.len());
            assert(forall(|i: int| 0 <= i < index ==> arr[min_second_index as int][1] <= arr[i][1]));
        }

        arr[min_second_index][0]
    }
}

// Score: (0, 1)
// Safe: True