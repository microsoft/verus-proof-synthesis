Your mission is to add proper loop invariants to the loop before the target ```assert``` statement.

Just as verifying functions requires some effort to write appropriate preconditions and postconditions, verifying loops requires effort to write loop invariants.

Loop invariants have to be neither too weak nor too strong, so that:

1) the invariants hold upon the initial entry to the loop (e.g. in the loop example below, ```idx <= n``` holds for the initial value ```idx = 0```)

2) the invariant still holds at the end of the loop body, so that the invariant is maintained across loop iterations

3) the invariant is strong enough to prove the properties we want to know after the loop exits (e.g. to prove the assert statement and hence the loop_triangle’s postcondition in the example below)

Verus verifies the loop separately from the function that contains the loop.
This means that the proof of a loop does not automatically inherit function
preconditions or any properties established before the loop, like
```triangle(n as nat) < 0x1_0000_0000``` from the surrounding function in the example below.
If the loop relies on these preconditions or any properties established before
the loop, they must be listed explicitly in the loop invariants.

Verus does allow you to opt-out of this behavior, meaning that your loops will
inherit information from the surrounding context. This will simplify your loop invariants,
but verification time may increase for medium-to-large functions.
You can do so by adding the #![verifier::loop_isolation(false)] attribute to the
 module or the root of the crate.

```
fn loop_triangle(n: u32) -> (sum: u32)
    requires
        triangle(n as nat) < 0x1_0000_0000,
    ensures
        sum == triangle(n as nat),
{
    let mut sum: u32 = 0;
    let mut idx: u32 = 0;
    while idx < n
        invariant
            idx <= n,
            sum == triangle(idx as nat),
            triangle(n as nat) < 0x1_0000_0000,
        decreases n - idx,
    {
        idx = idx + 1;
        assert(sum + idx < 0x1_0000_0000) by {
            triangle_is_monotonic(idx as nat, n as nat);
        }
        sum = sum + idx;
    }
    assert(sum == triangle(n as nat));
    sum
}
```

Note that, the loop above has a ```decreases``` clause. It is used to help Verus
prove the loop will terminate.
