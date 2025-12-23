
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


//         assert(sum + (arr[( index ) as int] as i128) <= i128::MAX && sum + (arr[( index ) as int] as i128) >= i128::MIN);
//   assertion failed: sum + (arr[( index ) as int] as i128) <= i128::MAX && sum + (arr[( index ) as int] as i128) >= i128::MIN

// Compilation Error: False, Verified: 1, Errors: 0, Verus Errors: 0
// Safe: False