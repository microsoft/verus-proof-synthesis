Failed assertion
```
Line 11-11:
    assert(exists|i: int| #[trigger] is_even(i));
```

Code
```
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
```
