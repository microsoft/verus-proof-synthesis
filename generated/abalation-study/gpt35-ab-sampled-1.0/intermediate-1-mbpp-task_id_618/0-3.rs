
use vstd::prelude::*;

fn main() {}

verus! {

    #[verifier::trigger]
    #[inline(always)]
    const fn safe_division(a: u32, b: u32) -> u32 {
        requires
            b != 0,
        ensures
            i32::MIN <= result as i32 <= i32::MAX,
        { a / b }
    }

    fn element_wise_divide(arr1: &Vec<u32>, arr2: &Vec<u32>) -> (result: Vec<u32>)
        requires
            arr1.len() == arr2.len(),
            forall|i: int| 0 <= i < arr2.len() ==> arr2[i] != 0,
            forall|i: int| (0 <= i < arr1.len()) ==>
                (i32::MIN <= arr1[i] / arr2[i] as i32 <= i32::MAX),
        ensures
            result@.len() == arr1@.len(),
            forall|i: int| 0 <= i < result.len() ==> result[i] == (arr1[i] / arr2[i]),
    {
        let mut output_arr = Seq::empty();

        let mut index = 0;
        while (index < arr1.len())
            invariant
                0 <= index <= arr1.len(),
                arr1.len() == arr2.len(),
                forall|i: int| 0 <= i < index ==> arr2[i] != 0,
                forall|i: int| 0 <= i < index ==> i32::MIN <= arr1[i] / arr2[i] as i32 <= i32::MAX,
                output_arr.len() == index,
                forall|i: int| 0 <= i < output_arr.len() ==> output_arr.index(i) == arr1[i] / arr2[i],
        {
            let value = safe_division(arr1[index], arr2[index]);
            output_arr = output_arr.push(value);
            index += 1;
        }
        output_arr
    }
} // verus!

// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1