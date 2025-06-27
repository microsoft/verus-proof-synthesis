use vstd::prelude::*;
fn main() {}

verus! {

spec fn is_even(n: u32) -> bool {
    (n % 2) == 0
}

fn is_product_even(arr: &Vec<u32>) -> (result: bool)
    ensures
        result <==> (exists|k: int| 0 <= k < arr.len() && is_even(#[trigger] arr[k])),
{
    let mut index = 0;
    while index < arr.len()
        invariant 
            index <= arr.len(),
            arr.len() < 100, // assumed logical limit to prevent overflow or unwarranted conditions
            forall |j:int| 0 <= j < index ==> !is_even(arr[j]),
    {
        if (arr[index] % 2 == 0) {
            return true;
        }
        index += 1;
    }
    false
}

} // verus!
// is safe: True
// Score: Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 1