
use vstd::prelude::*;
fn main() {}

verus! {

proof fn bound_check(x: u32, y: u32)
    requires
        x <= 0xffff,
        y <= 0xffff,
    ensures
        x * y <= 0x100000000,
{
    let x_u64: u64 = x as u64;
    let y_u64: u64 = y as u64;
    assert(x_u64 <= 0xffff as u64);
    assert(y_u64 <= 0xffff as u64);
    let maxrack: u64 = 0xffff as u64;
    assert(x_u64 * y_u64 <= maxrack * maxrack);
    assert(maxrack * maxrack <= 0xFFFFFFFF as u64);
    assert(x_u64 * y_u64 <= 0xFFFFFFFF as u64);
}
}

The function `bound_check` is supposed to verify that the product of `x` and `y` does not exceed `0x100000000`, which is `2^32`. The loop converts `x` and `y` into `u64` to prevent overflow during multiplication, which makes sense.

Let's break down what each part is doing:

1. **Requirements**:
   - `x` and `y` are both less than or equal to `0xffff` (which is `65535` in decimal). This means they are 16-bit values.

2. **Ensures**:
   - The product `x * y` should be less than or equal to `0x100000000` (`4294967296` in decimal), which is `2^32`.

3. **Body**:
   - Converts `x` and `y` to `u64`.
   - Asserts that `x_u64` and `y_u64` are within the 16-bit range.
   - Defines `maxrack` as `0xffff` in `u64`.
   - Asserts that the product `x_u64 * y_u64` is less than or equal to `maxrack * maxrack`.
   - Asserts that `maxrack * maxrack` is less than or equal to `0xFFFFFFFF`.
   - Finally, asserts that `x_u64 * y_u64` is less than or equal to `0xFFFFFFFF`.

Now, looking at the assertions:

- `maxrack * maxrack` would be `(0xffff) * (0xffff) = 0xfffffffe0001` in hexadecimal, which is `4294967295` in decimal.
- `0xFFFFFFFF` is `4294967295`, so `maxrack * maxrack <= 0xFFFFFFFF` is true.

However, the problem is that `x_u64 * y_u64 <= maxrack * maxrack` can be larger than `0x100000000` because `0xffff * 0xffff = 0x100000000 - 1 = 4294967295`, which is just under `0x100000000`.

Wait, but let's calculate:

- `0xffff * 0xffff = 0x100000000 - 1`
- So, `x_u64 * y_u64` is less than or equal to `0x100000000 - 1`
- Therefore, it should be less than `0x100000000`

But why is the assertion failing?

Looking back at the code, the `ensures` clause specifies that `x * y <= 0x100000000`, but in the last assertion, it's checking against `0xFFFFFFFF`, which is `4294967295`. So, perhaps there's a confusion here.

Wait, `0x100000000` is `4294967296`, and `0xFFFFFFFF` is `4294967295`. They are almost the same, but `0x100000000` is one more than `0xFFFFFFFF`.

In the `ensures` clause, `x * y <= 0x100000000` allows for the maximum value to be `4294967296`. However, the product `x_u64 * y_u64` is being compared against `0xFFFFFFFF`, which is `4294967295`, which is smaller. So, if `x_u64 * y_u64` is precisely `4294967296`, the assertion against `0xFFFFFFFF` would fail.

But wait, `x` and `y` are both `u32` and less than or equal to `0xffff`, so their product can be up to `0x100000000 - 1`, which is `4294967295`. Therefore, `x_u64 * y_u64` should not exceed `0xFFFFFFFF`.

Wait, that seems conflicting. If `x` and `y` are each at most `0xffff` (`65535`), then their product is at most `0xffff * 0xffff = 0x100000000 - 1 = 4294967295 = 0xFFFFFFFF`. So, why is there an assertion `x * y <= 0x100000000`? Perhaps this is a mistake, and it should be `0xFFFFFFFF`.

Alternatively, the confusion could be between `0x100000000` and `0xFFFFFFFF`. `0x100000000` is `2^32`, which is indeed bigger than `0xFFFFFFFF`.

So, perhaps the issue is that in the `ensures` clause, the product is allowed to be up to `0x100000000`, but in reality, with `x` and `y` up to `0xffff`, the maximum product is `0xFFFFFFFF`. Therefore, the assertion `x_u64 * y_u64 <= 0xFFFFFFFF` should always hold.

But in the code, it's checking `x_u64 * y_u64 <= maxrack * maxrack`, and `maxrack` is `0xffff`. So, `maxrack * maxrack` is `0xffff * 0xffff = 0x100000000 - 1 = 0xFFFFFFFF`.

So, why is the assertion failing?

Maybe the issue is that when converting from `u32` to `u64`, the types are causing unexpected behavior. For example, in Verus or Rust, any unsigned integer can overflow when performing operations, but since` x` and `y` are `u32`, their values are capped, so converting to `u64` should not cause overflow.

Another possibility is that during multiplication, even though `x` and `y` are within `0xffff`, their product as `u64` could potentially spill over into a higher bit that affects the comparison.

Wait, but in this case, `x` and `y` are both `16`-bit values, so their product, as `u64`, should fit within `32` bits, and thus `maxrack * maxrack` should be sufficient.

So, maybe the issue is in how Verus handles the proof. Perhaps the `assert(x_u64 * y_u64 <= maxrack * maxrack);` is not automatically proven, and Verus requires additional information or proof steps to verify this.

To fix this, I can try adding a proof step that demonstrates that `x_u64 * y_u64 <= maxrack * maxrack`. Perhaps using arithmetic or inequalities to make this explicit.

Here's what I can do:

1. Since `x` and `y` are bounded by `0xffff`, their `u64` counterparts `x_u64` and `y_u64` are also bounded by `0xffff` as `u64`.

2. Therefore, `x_u64 * y_u64` will be less than or equal to `(0xffff as u64) * (0xffff as u64) = maxrack * maxrack = 0x1000000000000 - 1`.

But wait, in `u64`, 0xffff is `65535`, so 0xffff * 0xffff is indeed `4294967295`, which is less than `0x100000000` (`4294967296`).

So, `x_u64 * y_u64` should always be less than or equal to `maxrack * maxrack`.

But perhaps Verus needs more explicit steps to understand this.

I can add a proof step to explicitly assert the bounds on `x_u64` and `y_u64` again and then derive the bound on their product.

Another approach is to use the fact that `maxrack` is the maximum value for `x_u64` and `y_u64`, so multiplying them gives the maximum possible product.

Alternatively, since Verus is similar to Rust and SMT solvers, it might not automatically infer these arithmetic properties. So, adding an explicit assertion or a lemma that proves that the product is bounded could help.

Let me try adding explicit bounds and then show the multiplication.

I'll modify the proof function to include these steps:

rust
proof fn bound_check(x: u32, y: u32)
    requires
        x <= 0xffff,
        y <= 0xffff,
    ensures
        x * y <= 0x100000000,
{
    let x_u64: u64 = x as u64;
    let y_u64: u64 = y as u64;
    assert(x_u64 <= 0xffff as u64);  // x is <= 0xffff as u32, so as u64, it's <= 0xffff
    assert(y_u64 <= 0xffff as u64);  // same for y
    let maxrack: u64 = 0xffff as u64;
    assert(maxrack * maxrack == 0xffffe0000001 as u64);  // Calculate maxrack^2
    assert(x_u64 * y_u64 <= maxrack * maxrack);  // x*y is <= maxrack^2
    assert(maxrack * maxrack == 0xFFFFFFFF as u64);  // Wait, 0xffff * 0xffff is 0x100000000 - 1 = 0xFFFFFFFF
    assert(x_u64 * y_u64 <= 0xFFFFFFFF as u64);
}

But wait, `0xffff as u64` multiplied by `0xffff as u64` equals `18446744073709551616 - 1 = 18446744010406233601`, which is `0x100000000 * 0x100000000 - 1`, which doesn't seem right.

Wait, perhaps I made a mistake in calculating `maxrack * maxrack`.

Wait, `maxrack` is `0xffff` as `u64`, so it's `65535` in decimal.

65535 * 65535 = ?

Let me calculate:

65535 * 65535 = (65536 - 1) * (65536 - 1) = 65536^2 - 2*65536 + 1

65536^2 = 4294967296 (which is 0x100000000 in hex)

So, 4294967296 - 2*65536 + 1 = 4294967296 - 131072 + 1 = 4294836225

Wait, 4294967296 minus 131072 is 4294836224, plus 1 is 4294836225.

In hex, 4294836225 is 0xFFFE0001.

Wait, that doesn't make sense because 0xffff * 0xffff is 0xfffe0001, which is 4294836225.

But earlier, I thought that 0xffff * 0xffff was 0xffffffff, which is 4294967295.

There's a mistake here. Let's clarify:

In hexadecimal:

0xffff * 0xffff = ?

Let's compute it:

0xffff is 65535 in decimal.

65535 * 65535 = 4,294,836,225

In hexadecimal, that's 0xFFFE0001.

Wait, no, 0xFFFF * 0xFFFF is 0x10000 * 0xFFFF - 0xFFFF = 0x10000*0xFFFF - 0xFFFF = 0xFFFE0000 - 0xFFFF = 0xFFFE0000 - 0x0000FFFF = 0xFFFE0000 - 0x0000FFFF = 0xFFFE0000 - 0xFFFF = 0xFFFE0000 - 0xFFFF = 0xFFFE0000 - 0xFFFF = 0xFFFE0000 - 0xFFFE = Wait, no, that's incorrect.

Let me compute 0xffff * 0xffff:

0xffff * 0xffff = (0x10000 - 1) * (0x10000 - 1) = 0x10000^2 - 2*0x10000 + 1 = 0x100000000 - 0x20000 + 1 = 0x100000000 - 0x20000 is 0xFFFE0000, plus 1 is 0xFFFE0001.

So, 0xffff * 0xffff = 0xFFFE0001 in hex, which is 4294836225 in decimal.

But earlier, I thought that 0xffff * 0xffff was 0xFFFFFFFF, which is 4294967295.

So, there's a discrepancy. This suggests that my initial assumption was wrong.

But wait, in decimal, 0x100000000 is 4294967296.

0xFFFF * 0xFFFF = 0xFFFE0001 = 4294836225, which is less than 0x100000000 - 1 = 4294967295.

So, that means that the product of `x` and `y` is actually less than or equal to 0xFFFE0001, which is less than 0xFFFFFFFF.

But that contradicts my earlier understanding that `x` and `y` being 16-bit values would have a product that fits within 32 bits. It seems that the product is actually less than 0x100000000 by a significant margin.

Given this, perhaps the original assertion `x_u64 * y_u64 <= maxrack * maxrack` is correctFOO.

But then why is the assertion failing? Maybe because Verus doesn't see the connection.

I think the issue is that when converting `x` and `y` to `u64`, the multiplication `x_u64 * y_u64` may overflow the `u64` type, causing unexpected behavior.

Wait, but `u64` is sufficient to hold the product of two `u32` numbers, right? Because `2^32 * 2^32 = 2^64`, which is exactly the maximum value for `u64`.

But in this case, `x` and `y` are both `u32` and less than or equal to `0xffff`, so their product is at most `0xffff * 0xffff = 0xFFFE0001`, which is less than `2^32` (0x100000000). So, their product can fit within a `u32` or a `u64`.

Alternatively, perhaps in Verus, the types are causing the multiplication to be treated differently.

To fix this, I can try to bound `x_u64 * y_u64` before comparing it to `maxrack * maxrack`.

Let me insert an explicit assertion that `x_u64 * y_u64` is less than or equal to `maxrack * maxrack`.

So, in the code, after defining `maxrack`, I'll add:

rust
assert(x_u64 * y_u64 <= maxrack * maxrack);


//     assert(x_u64 * y_u64 <= maxrack * maxrack);
//   assertion failed: x_u64 * y_u64 <= maxrack * maxrack

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 365
// Safe: False