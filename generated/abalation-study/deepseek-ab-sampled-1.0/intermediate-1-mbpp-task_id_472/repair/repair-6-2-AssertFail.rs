
use vstd::prelude::*;

fn main() {}

verus! {

spec fn is_even(n: int) -> bool {
    n % 2 == 0
}

proof fn test_exists_succeeds() {
    assert(is_even(4)); // Added example of an even integer
    assert(exists|i: int| #[trigger] is_even(i));
}

}


//         assert(forall|i: int, j: int| 0 <= i < j < arr.len() && j == i + 1 ==> arr[i] + 1 == arr[j]); // Added by AI
//   assertion failed: forall|i: int, j: int| 0 <= i < j < arr.len() && j == i + 1 ==> arr[i] + 1 == arr[j]

// Compilation Error: False, Verified: 1, Errors: 0, Verus Errors: 0
// Safe: False