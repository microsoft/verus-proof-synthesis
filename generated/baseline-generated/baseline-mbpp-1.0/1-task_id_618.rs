use vstd::prelude::*;

fn main() {}

verus! {
    fn element_wise_divide(arr1: &Vec<u32>, arr2: &Vec<u32>) -> (result: Vec<u32>)
        requires
            arr1.len() == arr2.len(),
            forall |i: int| 0 <= i < arr2.len() ==> arr2[i] != 0,
            forall |i: int| 0 <= i < arr1.len() ==> (i32::MIN <= #[trigger] (arr1[i] / arr2[i]) <= i32::MAX),
        ensures
            result@.len() == arr1@.len(),
            forall |i: int| 0 <= i < result.len() ==> #[trigger] result[i] == #[trigger] (arr1[i] / arr2[i]),
    {
        let mut output_arr = Vec::with_capacity(arr1.len());
        let mut index = 0;
        proof {
            assert(0 <= output_arr@.len() <= arr1@.len());
        }
        while index < arr1.len()
        invariant
            0 <= index <= arr1.len(),
            output_arr.len() == index,
            arr1@.len() == arr2@.len(),
            forall |i: int| 0 <= i < arr2@.len() ==> arr2[i] != 0,
            forall |i: int| 0 <= i < output_arr@.len() ==> #[trigger] output_arr[i] == #[trigger] (arr1[i] / arr2[i]),
        {
            output_arr.push(arr1[index] / arr2[index]);
            // proof block to maintain invariants after push operation
            proof {
                assert(output_arr.len() == index + 1);
                assert(forall |i: int| 0 <= i < output_arr@.len() ==> #[trigger] output_arr[i] == #[trigger] (arr1[i] / arr2[i]));
                assert(0 <= (index + 1) <= arr1.len());
            }
            index += 1;
            // proof block to maintain invariants for the new index value
            proof {
                assert(0 <= index <= arr1.len());
            }
        }
        output_arr
    }
}
// Score: (2, 0)
// Safe: False