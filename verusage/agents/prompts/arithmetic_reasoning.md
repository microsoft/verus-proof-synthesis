Your mission is to help the verifier prove the given failed assertion using arithmetic reasoning.

## Step 1: Understand Verus arithmetic reasoning features

Nonlinear arithmetic is arithmetic that involves the operators `*`, `/`, and/or `%` on integer variables. Verus can reason about nonlinear arithmetic (e.g., it can reason that `x * (y * z) == (x * y) * z`), but it needs to be explicity told when to do so using `by(nonlinear_arith)`.

**IMPORTANT:** The verifier does ***not*** automatically propagate to the nonlinear-arithmetic solver any facts from the context about variables, such as from preconditions or variable assignments. So, any facts the solver needs to know about about variables in the asserted fact ***must*** be included in a `requires` clause following `by(nonlinear_arith)`.

Examples:
```rust
pub proof fn test_commute(x: u32, y: u32) {
    assert(x * y == y * x); // FAILS
    assert(x * y == y * x) by (nonlinear_arith); // SUCCEEDS
    // note: no requires from context needed
}
```
```rust
pub proof fn test_distrib(x: u32, a: u32, b: u32)
    requires
        x == 2
{
    assert(x * (a + b) == 2 * a + 2 * b) by (nonlinear_arith); // FAILS
    assert(x * (a + b) == 2 * a + 2 * b) by (nonlinear_arith)
        requires
            x == 2
        ; // SUCCEEDS
}
```
```rust
pub proof fn test(x: int, y: int, w: int, z: int)
    requires
        0 <= x <= y,
        0 <= z <= w
{
    assert(x * z <= y * w) by (nonlinear_arith); // FAILS
    assert(x * z <= y * w) by (nonlinear_arith)
        requires
            0 <= x <= y,
            0 <= z <= w; // SUCCEEDS
}
```

## Step 2: Identify reasoning steps

Identify reasoning steps needed to transform the failing assertion into a succeeding one. There may be multiple reasoning steps involved.
- **Important**: Be very explicit about each step in the arithmetic reasoning. For instance, if it involves a sequence of equalities or inequalities, state each such equality or inequality explicitly, not skipping what seem like obvious steps. Include simplification or rewriting of subexpressions as well.
- **REASON ON BINARY SUBEXPRESSIONS**: When reasoning about an expression with many operators, reason about only a single **binary** subexpression at a time. This will help the verifier succeed on less complex expressions without timing out.
- ***INCLUDE ASSOCIATIVITY AND COMMUTATIVITY***: ALWAYS include assertions for equalities such as associativity and commutativity. Verus does not know these axioms by default, so you must explicitly invoke nonlinear arithmetic!
  - Remember that `x * y * z` is parsed as `(x * y) * z`.
- If the failing assertion already uses `by (nonlinear_arith)`, break the reasoning into simpler steps.
- Use good style by replacing isolated failing assertions using an `assert(...) by {...}` block. Use `assert(...) by {...}` to nest any reasoning about subexpressions.

Use assertions for each step in your equational reasoning. Example:
Before:
```rust
assert(x * y * z * (a + b) == x * (z * y * a + z * y * b)); // FAILS
```
After:
```rust
assert(x * y * z * (a + b) == x * (z * y * a + z * y * b)) by {
    // reason on subexpr
    assert(((x * y) * z) * (a + b) == (x * (y * z)) * (a + b)) by {
        // associativity
        assert((x * y) * z == x * (y * z)) by (nonlinear_arith);
    }
    // associativity
    assert((x * (y * z)) * (a + b) == x * ((y * z) * (a + b))) by (nonlinear_arith);
    // reason on subexpr
    assert(x * ((y * z) * (a + b)) == x * ((z * y) * (a + b))) by {
        // commutativity
        assert(y * z == z * y) by (nonlinear_arith);
    }
    // reason on subexpr
    assert(x * ((z * y) * (a + b)) == x * (((z * y) * a + (z * y) * b))) by {
        // distributivity
        assert((z * y) * (a + b) == ((z * y) * a + (z * y) * b)) by (nonlinear_arith);
    }
} // SUCCEEDS
```

## Step 3: Include all facts about variables in `requires`
- Determine what facts are known about variables in a nonlinear arithmetic expression. Check preconditions, let statements, etc.
- Include all such facts in a `requires` clause following `by (nonlinear_arith)`.
- Remember that the verifier does not include information from the context in `nonlinear_arith` expressions. You must remember to add this in a `requires` clause!

Example:
```rust
pub proof fn test(x: int)
    requires
        x > 0
{
    let y: int = x + 2;
    assert(y * x / (x + 2) == x); // FAILS
    assert(y * x / (x + 2) == x) by (nonlinear_arith); // FAILS
    assert(y * x / (x + 2) == x) by (nonlinear_arith)
        requires
            y == x + 2,
            x > 0; // SUCCEEDS
}
```
