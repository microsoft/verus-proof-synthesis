
use vstd::prelude::*;
fn main() {}

verus! {

spec fn is_even(n: int) -> bool {
    n % 2 == 0
}

proof fn test_exists_succeeds() {
    assert(is_even(4));
    assert(exists|i: int| #[trigger] is_even(i));
}

}


//             assert(result@.len() <= arr1.len());
//   assertion failed: result@.len() <= arr1.len()

// Compilation Error: False, Verified: 1, Errors: 0, Verus Errors: 0
// Safe: False