
use vstd::prelude::*;

fn main() {}

verus! {

proof fn div_bounds_prop(
    dividend: u32, 
    divisor: u32
)
    requires 
        divisor != 0,
    triggers 
        dividend / divisor,
    ensures
        i32::MIN <= dividend / divisor <= i32::MAX,
{
    assert(i32::MIN <= dividend / divisor && dividend / divisor <= i32::MAX);
}

fn element_wise_divide(arr1: &Vec<u32>, arr2: &Vec<u32>) -> (result: Vec<u32>)
    requires
        arr1.len() == arr2.len(),
        forall |i:int| 0 <= i < arr2.len() ==> arr2[i] != 0,
        forall |i:int|
            (0 <= i < arr1.len()) ==> div_bounds_prop(arr1[i], arr2[i]),
    ensures
        result@.len() == arr1@.len(),
        forall |i:int|
            0 <= i < result.len() ==> result[i] == arr1[i] / arr2[i],
{
    let mut output_arr = Vec::with_capacity(arr1.len());
    let mut index = 0;

    assert(output_arr.len() == 0);

    while index < arr1.len()
        invariant
            output_arr.len() == index,
            0 <= index <= arr1.len(),
    {
        output_arr.push(arr1[index] / arr2[index]);
        index += 1;
    }
    output_arr
}

} // verus!

// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1