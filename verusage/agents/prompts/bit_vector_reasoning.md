Your mission is to help the verifier prove facts which involve reasoning about bitwise operations.

## Step 1: Understand Verus bit vector reasoning features

Bitwise reasoning involves equations that use bitwise operations `&`, `|`, `^`, `<<` and `>>`, and bounded integer operations `add`, `sub`, `mul`, `wrapped_add`, `checked_add`, etc. Verus can reason about bitwise operations, but it needs to be explicity told when to do so using `by(bit_vector)`.

**Note:** bit vector reasoning must use named integer operations `add`, `sub`, `mul`, instead of `+`, `-`, `*`, because the former use bounded integers while the latter do not.

**IMPORTANT:** this command does ***not*** propagate any facts from the context about variables, such as from preconditions or variable assignments. So, any facts about variables in a bitwise expression ***must*** be included in the `requires` clause.

Examples:
```rust
proof fn test_passes(b: u32) {
    assert(b & 7 == b % 8) by (bit_vector); // SUCCEEDS
    assert(b & 0xff < 0x100) by (bit_vector); // SUCCEEDS
    // note: no requires from context
}
```
```rust
proof fn test_and(x: u32, y: u32)
  requires x == y
{
    assert(x & 3 == y & 3) by (bit_vector);  // FAILS
    assert(x & 3 == y & 3) by (bit_vector)
        requires
            x == y,
    ;  // SUCCEEDS
}
```

**IMPORTANT:** You CANNOT use a spec fn inside an expression with `by (bit_vector)`. Instead, inline the definition of the spec function inside the assertion using `by (bit_vector)`.

Example:
```rust
spec fn get_bit(a: u32, b: u32) -> bool {
    (0x1u32 & (a >> b)) == 1
}

proof fn test_macro(x: u32)
    requires x & 2 == 1
{
    assert(get_bit(x, 1)) by (bit_vector)
        requires
            x & 2 == 1
    ; // COMPILATION ERROR
    assert(get_bit(x, 1)) by {
        assert((0x1u32 & (x >> 1)) == 1) by (bit_vector)
            requires
                x & 2 == 1
        ; // SUCCEEDS
    }
}
```

**IMPORTANT:** You CANNOT use a constant variable inside `by (bit_vector)`. Instead, assign the constant variable to another ghost variable, and then use `by (bit_vector)` on the expression that involves that ghost variable.

Example:
```rust
    pub const MYCONST: u32 = 10;

    let ghost tmp = MYCONST; //needed here!

    assert( tmp & 3 == 10 & 3) by (bit_vector)
        requires
            tmp == 10,
    ; // MYCONST cannot be directly used here, as bit_vector prover does NOT support const
```



## Step 2: Identify all facts about variables for `requires`
- Determine what facts are known about variables in the bitwise expression.
- Check preconditions and let statements. Make sure to include at facts for **all** variables in the expression!
- Include all facts in `requires` clause for `by (bit_vector)`.
- Remember that the verifier does not include information from the context in `bit_vector` expressions. You must remember to add this in `requires` clauses!

Example:

Before:
```rust
spec fn max(n: u64, m: u64) -> bool {
    (n << 1) < m
}

proof fn test(a: u64, b: u64)
    requires
        a < 32,
        b <= a
    ensures
        ({
            let x = add(a, b);
            max(x, 128)
        })
{
    let x = add(a, b);
    // BELOW ASSERTION FAILS
    assert(max(x, 128));
}
```
Diff:
```rust
<<<<<<< SEARCH
    assert(max(x, 128));
=======
    assert(max(x, 128)) by {
        assert((x << 1) < 128) by (bit_vector)
            requires
                a < 32,
                b <= a,
                x == add(a, b)
        ;
    }
>>>>>>> REPLACE
```
Comments:
- We proved the failing assertion using `by (bit_vector)`.
- We added `requires` clauses for all variables. Note that `x` appears in the expression, but its value depends on `a` and `b`, so those are included as well.
- We inlined the definition of `max` because we cannot use spec functions in a `by (bit_vector)` assertion.
