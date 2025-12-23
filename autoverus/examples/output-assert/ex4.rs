use vstd::prelude::*;
fn main() {}

verus! {

spec fn is_even(n: int) -> bool {
    n % 2 == 0
}

proof fn test_exists_succeeds() {
    assert(is_even(4)); // Added by AI, for assertion fail
    assert(exists|i: int| #[trigger] is_even(i));
}

}
