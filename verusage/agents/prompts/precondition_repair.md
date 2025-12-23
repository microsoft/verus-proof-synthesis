Your mission is to address the precondition not satisfied error for the following code. For each failing precondition at the function call site, add proof blocks or assertions just before the function invocation to establish the required precondition. It is okay if the assertions will not pass verification initially, you will address those in subsequent debugging steps.

Don't use `assume`.
If the function to be changed is `proof fn`, please don't include any `proof {...}` block, just use `assert(...)`.
**IMPORTANT**: DO NOT modify the `requires` or `ensures` clauses of any function. You should only add proof blocks or assertions in the function body.

If a failed precondition contains a conjunction and we do not know which conjunct in the conjunction is failing,
please split the conjunction into multiple assertions with each assertion about one conjunct. This will help
follow-up proof development to identify and focus on the failing conjunct.

For example, consider the following toy function that calls another function with preconditions:

```
proof fn bar(x: int, y: int)
requires
    x < 10,
    x > y,
    x + y > 0,
{
    ...
}

proof fn foo(a: int, b: int)
requires ...
ensures ...
{
    ...
    bar(a, b);  // Precondition not satisfied
    ...
}
```

If `bar`'s precondition is not satisfied at the call site in `foo`, we can fix it by adding assertions just before the call:

```
proof fn foo(a: int, b: int)
requires ...
ensures ...
{
    ...
    assert(a < 10);
    assert(a > b);
    assert(a + b > 0);
    bar(a, b);
    ...
}
```

(If `foo` is an executable function, the assertions should be put inside `proof{...}` blocks.)

Note that using three separate asserts is much better than using one assert on a big conjunction, like
```assert( (a < 10) && (a > b) && (a + b > 0))```

## Additional Guidelines:

1. **Identify which precondition is failing** at the call site.
2. **Look at what information is available**: function preconditions, loop invariants, previous assertions, or established facts.
3. **Add assertions or proof blocks before the function call** that establish the required precondition step by step.
4. **Reference relevant spec functions, loop invariants, or function preconditions** as needed to build the proof.

## Handling preconditions inside loops:

If the precondition error occurred inside a loop, you may need to add loop invariants to help Verus prove the precondition will always be satisfied. Here's how loop invariants look in Verus:

```
let mut x = 1;

while x < 10
    invariant
        x >= 1,
        x <= 10,
{
    x = x + 1;
}
```
