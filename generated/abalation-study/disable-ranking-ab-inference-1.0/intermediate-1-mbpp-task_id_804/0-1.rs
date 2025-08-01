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
            exists|k: int| 0 <= k < index && is_even(arr[k]) ==> result,
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
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1