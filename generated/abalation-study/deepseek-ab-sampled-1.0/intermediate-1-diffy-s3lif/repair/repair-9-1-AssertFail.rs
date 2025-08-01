

use vstd::prelude::*;
fn main() {}

verus! {

spec fn is_even(n: int) -> bool {
    n % 2 == 0
}

proof fn test_exists_succeeds() {
    assert(is_even(2));
    assert(exists|i: int| #[trigger] is_even(i));
}

}

//             assert(a[( i ) as int] == 4); // Adds assertion in proof block
//   assertion failed: a[( i ) as int] == 4

// Compilation Error: False, Verified: 1, Errors: 0, Verus Errors: 0
// Safe: False