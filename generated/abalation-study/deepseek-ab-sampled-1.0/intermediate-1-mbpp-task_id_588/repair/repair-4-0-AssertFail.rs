
use vstd::prelude::*;
fn main() {}

verus! {

spec fn is_even(n: int) -> bool {
    n % 2 == 0
}

proof fn test_exists_succeeds() {
    assert(exists|i: int| #[trigger] is_even(i));
}

}


//     assert(i32::MIN <= (max_val - min_val) && (max_val - min_val) <= i32::MAX) by {
//   assertion failed: i32::MIN <= (max_val - min_val) && (max_val - min_val) <= i32::MAX

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1
// Safe: False