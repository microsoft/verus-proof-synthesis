Your mission is to fix the "post-condition not satisfied error" for the provided code. Please follow these steps:

Step 1: Add a proof block at or just before the function exit point where the post-condition failure occurred.
Step 2: In this proof block, for each failed post-condition clause, add a corresponding assert statement.
Step 3: If any asserted post-condition clause depends on variables that are not yet defined, define those variables immediately before the assert.

Note:
1. The function's ensures block may contain multiple post-conditions, and some post-conditions may have several conjunctive clauses. Do NOT assert all of them—only assert the clauses that have actually failed.

2. If a failed post-condition contains a conjunction and we do NOT know which conjunct in the conjunction is failing,
please split the conjunction into multiple assertions with each assertion about one conjunct. This will help
follow-up proof development to identify and focus on the failing conjunct.

For example, consider the following toy function
```
proof fn foo (...)
requires ...
ensures
           ({
                let x = ...
                let y = ...
                let z = ...
                &&& x < 10
                &&& x > y
                &&& z > x + y
            }),
{
...
}
```

If ```foo```'s post-condition is not satisfied, we can fix it by adding the following code block at the end of ```foo```:
```
    {
        let x = ...
        let y = ...
        let z = ...
        assert(x < 10);
        assert(x > y);
        assert(z > x + y);
    }
```
(If ```foo``` is an executable function, the above code block should be put inside ```proof{...}```.)

Note that using three separate asserts is much better than using one assert on a big conjunction, like
```assert( (x < 10) && (x > y) && (z > x + y))```

**Important Guidelines:**
- Use `if-else` statements to handle different cases, instead of using `match` statements with `_` patterns.
