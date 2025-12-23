Your mission is to fix the assertion error by providing proper quantifier instantiation using proof blocks.

Transform `assert(forall |x| ==> P(x));` to `assert forall |x| implies P(x) by { ... }`

For example,
```verus
assert(forall |x| P(x) ==> Q(x));
```
should be transformed to
```verus
assert forall |x| P(x) implies Q(x) by {
    assert(Q(x));
}
```

Guidelines:
- Use `implies` instead of `==>` in the transformed assertion.
- NEVER use `fix`, `assume`, `intro`, or `show` inside the proof block, as these are not valid in Verus proof blocks. Note that within the example `assert forall ... by { }` proof block above, the antecedent `P(x)` is automatically assumed to be true within the proof block.
- Within the proof block, add assertion(s) for the consequent `Q(x)` using the instantiated variable `x`. **Do not add any extra assertions or do further simplification, just perform direct substitution.** You will have the opportunity to further develop the proof for each case in subsequent debugging steps.
- DO NOT inline the `P(x)` or `Q(x)`, since this would change the original semantics, especially for trigger pattern.

- If the original assert is like ```assert(xyz == forall |x| ==> P(x))```, you should NOT apply the instantiation directly, because
```assert(forall |x| ==> P(x))``` has different semantics from ```assert(xyz == forall |x| ==> P(x))```.
In fact, you may never be able to prove ```assert(forall |x| ==> P(x))```, if your goal is ```assert(xyz == forall |x| ==> P(x))```.
