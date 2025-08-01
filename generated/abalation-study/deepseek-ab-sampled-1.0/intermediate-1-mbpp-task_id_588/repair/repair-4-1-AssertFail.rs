

The failure occurred because the proof did not provide a specific example of an even integer. Adding a concrete example demonstrates the existence of such an integer.

use vstd::prelude::*;
fn main() {}

verus! {

spec fn is_even(n: int) -> bool {
    n % 2 == 0
}

proof fn test_exists_succeeds() {
    assert(is_even(4)); // Explicitly show that 4 is even
    assert(exists|i: int| #[trigger] is_even(i));
}

}

//     assert(i32::MIN <= (max_val - min_val) && (max_val - min_val) <= i32::MAX) by {
//   assertion failed: i32::MIN <= (max_val - min_val) && (max_val - min_val) <= i32::MAX

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False