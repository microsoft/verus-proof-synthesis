Failed assertion
```
Line 16-16:
        assert(i >= 2);
```

Code
```
use vstd::prelude::*;
fn main() {}

verus! {

fn while_loop(n: usize)
    requires
        n >= 2,
{
    let mut i = 2;
    while i < n
        invariant
            i <= n,
            n >= 2,
    {
        assert(i >= 2);
        i += 1;
    }
}

}
```
