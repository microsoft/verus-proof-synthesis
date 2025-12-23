Your mission is to help prove the failing assertion by adding a new integer_ring lemma to the current file.

## Step 1: Analyze where integer_ring lemma is needed

The ```integer_ring``` proof mode allows Verus to discharge the proof obligation using a dedicated algebra
solver called Singular, which is particularly good at proving nonlinear formulas that consist of a series of
congruence relations (i.e., equalities modulo some non-zero divisor n).

Keep in mind that, the integer_ring proof mode / Singular can only be used with ```int``` parameters; it
can NOT handle formulas that involve inequalities; it can NOT handle divisions; it can only prove modular
equivalence, instead of general equivalence.

The ```integer_ring``` proof mode can only be applied to a proof function with empty function body.

For example, this is one way to use integer_ring:
```rust
proof fn foo (a: int, b: int, c: int, n: int) by (integer_ring)
    requires
        n != 0,
        a % n == b % n,
    ensures
        (a * c) % n == (b * c) % n,
{}
```

And, this is another way to use integer_ring to a lemma function:
```rust
#[verifier::integer_ring]
proof fn foo (a: int, b: int, c: int, n: int)
    requires
        n != 0,
        a % n == b % n,
    ensures
        (a * c) % n == (b * c) % n,
{}
```

Note that, in both case, the proof function body has to be EMPTY!.

## Step 2: Determine to add an integer_ring lemma function or make the current function integer_ring

Option A:

If the failing assert property is basically the goal of the proof function, you can just empty the
current proof function body and apply integer_ring to the current proof function.

For example, Verus cannot prove the two ```assert``` statements in the lemma function below.
```rust
proof fn foo (a: int, b: int, c: int, n: int)
    requires
        n != 0,
        a % n == b % n,
    ensures
        (a * c) % n == (b * c) % n,
{
        if n > 0 {
            assert( (a * c) % n == (b * c) % n );
        } else {
            assert( (a * c) % n == (b * c) % n );
        }
}
```
Since, the target assert statements are essentially the post-condition of the current proof function, we
could just empty the current proof function body and apply integer ring:
```rust
#[verifier::integer_ring]
proof fn foo (a: int, b: int, c: int, n: int)
    requires
        n != 0,
        a % n == b % n,
    ensures
        (a * c) % n == (b * c) % n,
{}
```

Option B:
In other cases, if the failing assert that is related to integer modulo congruence is only part of the
current proof function, we should add a new helper lemma with ```#[verifier::integer_ring]``` mode.

When determine the signature for the new helper lemma by its pre- and postconditions, make sure to consider:
- What postcondition(s) are necessary to prove the failing assertion
- What preconditions are necessary to prove the postcondition
- What facts are true at the call-site of the helper lemma in the original proof and whether the preconditions would be satisfied

Remember to add ```#[verifier::integer_ring]``` to the new lemma function added.
