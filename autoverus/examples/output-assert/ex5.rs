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
            i >= 2, // Added by AI, for assertion fail
    {
        assert(i >= 2);
        i += 1;
    }
}

}
