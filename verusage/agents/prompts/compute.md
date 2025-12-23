If the given failed assertion `assert(e)` contains no variables and can therefore be computed by just evaluating spec functions and operators on constants, consider replacing it with `assert(e) by (compute)`. This is especially likely to help if `e` involves a recursive spec function, since the verifier can normally only expand a recursive function a small number of times due to fuel limits, but `by (compute)` isn't limited in this way.

Even if `e` contains a single variable `n`, it can still be useful to use `by(compute)`. Specifically, if `n` is known to lie in a range `a..b` containing a million or fewer values, then one can use `assert((a..b).all_spec(|n| e)) by(compute)`.

## Overview of proof `by (compute)`

`assert(e) by (compute)` runs an internal interpreter to simplify the asserted expression `e`.
When the expression involves computation on **constant values**, such as function invocation (including recursive function invocation), arithmetic operators, and logical operators, the internal interpreter can evaluate and simplify the entire constant part of the computation. You can use proof `by (compute)` for the following reasoning tasks:
- compute the value of a function for concrete (constant) arguments
- compute the value of a recursive function for concrete arguments
- compute the value of a function for a concrete range of integers

***Note:*** Proof `by (compute)` will not succeed if the asserted expression contains any variables. Make sure to invoke it with constants only! (Exception: See below for how to use `all_spec` when the expression contains exactly one variable.)

## How to use proof `by (compute)` for a constant expression

To use `by (compute)`, simply replace `assert(e)` with `assert(e) by (compute)`. **Make sure to replace any constant-valued variables in `e` with the constant value it is known to have.**

For example, suppose we know that `x == 17` and we want to assert that `add_three(x) == 20`. Do this by saying `assert(add_three(17) == 20) by (compute);`.

## Why `by (compute)` works well with recursive functions

Proof `by (compute)` is especially useful when the value being asserted involves a recursive function invocation. This is because `by (compute)` invokes an intepreter that will unfold recursive functions as many times as necessary to compute the asserted value. This is better than the normal Verus verification approach, which will only unfold a recursive function once.

## How to use proof `by (compute)` for a concrete range of integers

Normally you use `by (compute)` on expressions consisting only of constants, spec functions, and operators. However, you can also use it on an expression that contains a *single* integer variable, if the variable is known to lie in a range of a million or fewer values. In this case, you need to use the `all_spec` construct, as illustrated by the following example.

Imagine that we want to prove `assert(p(x))` for an integer variable `x` known to satisfy `1 <= x <= 100`. We do this with:
```rust
proof {
assert((1..101int).all_spec(|x| p(x))) by (compute);
let prop = |x| p(x);
assert(prop(x));
}
```

Note: the ```proof{...}``` above is needed when this part of the code is inside an executable function,
because ```let prop = |x| p(x);``` may contain non-Rust syntax features.
Of course, it would not be needed, if this part of the code is already inside a proof block or is inside
a proof function.

Note: when both ends of a range are constant values, we need to add type information for at least one of them, like `101int`.
However, if at least one of the end of a range is a variable, type annotation is NOT allowed.
For instance, `(1..a)` is correct; `(1..(a)int)` is WRONG.

The `all_spec` construct requires the import of the `RangeAll` module, which can be done by adding the following line at the beginning of the file if it isn't already there:
```rust
use vstd::compute::RangeAll;
```

Here's another example of a use of `by (compute)` for a concrete range of integers:

```rust
use vstd::compute::RangeAll;

spec fn p(u: usize) -> bool {
    u >> 8 == 0
}

proof fn range_property(u: usize)
    requires 25 <= u < 100,
    ensures p(u),
{
    // assert(p(u)) by (compute); <-- FAILS! Must invoke compute over range of concrete values
    assert((25..100int).all_spec(|x| p(x as usize))) by (compute);
    let prop = |x| p(x as usize);
    assert(prop(u));
}
```

## Example of applying `by(compute)` to a constant expression

```rust
pub const a: u32 = 3;
pub const b: u32 = 10;
pub const c: u32 = 2;

spec fn my_compute(x: u32) -> u32
{
    ((x % a + b) as u32) >> c
}

fn test(x: u32)
    requires
        x == 9
{
    assert(x == 9);
    // assert(my_compute(x) == 2) by (compute); <-- FAILS! substitute 9 for x instead
    assert(my_compute(9) == 2) by (compute);
}
```

## Example of applying `by(compute)` to an expression involving a recursive function
```rust
spec fn pow(base: nat, exp: nat) -> nat
    decreases exp,
{
    if exp == 0 {
        1
    } else {
        base * pow(base, (exp - 1) as nat)
    }
}

proof fn concrete_pow() {
    // assert(pow(2, 8) == 256); <-- FAILS! must use compute to unfold recursive function
    assert(pow(2, 8) == 256) by (compute);
}
```

## Complex example
```rust
spec fn pow(base: nat, exp: nat) -> nat
    decreases exp,
{
    if exp == 0 {
        1
    } else {
        base * pow(base, (exp - 1) as nat)
    }
}

proof fn pow_range(i: nat)
    requires
        pow(i, 2) == 256,
        1 <= i <= 100
    ensures
        i == 16
{
    assert((1..101int).all_spec(|x: int| x != 16 ==> pow(x as nat, 2) != 256)) by (compute);
    let prop = |x: int| x != 16 ==> pow(x as nat, 2) != 256;
    assert(prop(i as int));
}
```

## Guidelines
Consider the failing assertion. Analyze how `by (compute)` may help prove the assertion.
- Consider what constant values are available and what definitions are relevant to the unproven assertion.
- Consider if there are multiple reasoning steps that are missing. Break these into separate assertions `by (compute)`.

**Important:**
- Make sure to substitute concrete values for all variables before invoking `by (compute)`.
- Do NOT use a `requires` clause. `assert(...) by (compute)` does NOT allow any requires clause.
- Remember that `by (compute)` will unfold recusive functions as many times as necessary. This makes it more powerful than Verus's default verification approach.
- If the range involves two constant integers, a type annotation is needed for at least one of them, like `1..100int`.
If the start or the end of the range is a variable, no type annotation is needed; e.g., `1..end` is correct, `1..(end)int` is wrong.
- Let me repeat: you can only add type annotation after a constant value, NOT after a variable.
