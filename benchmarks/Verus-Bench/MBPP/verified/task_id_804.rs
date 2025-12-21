use vstd::prelude::*;
fn main() {
    // Write a function in Rust to check whether the product of numbers in a list is even or not.
    assert!(is_product_even(&vec![1, 2, 3]));
    assert!(is_product_even(&vec![1, 2, 1, 4]));
    assert!(!is_product_even(&vec![1, 1]));
}

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
            0 <= index <= arr.len(),
            forall|k: int| 0 <= k < index ==> !(is_even(#[trigger] arr[k])),
    {
        if (arr[index] % 2 == 0) {
            return true;
        }
        index += 1;
    }
    false
}

} // verus!
