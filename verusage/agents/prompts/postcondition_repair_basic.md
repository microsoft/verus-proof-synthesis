Your mission is to address the post-condition not satisfied error for the following code. For each failing postcondition, add an assertion at the end of the function body. It is okay if the assertions will not pass verification, you will address those in subsequent debugging steps.

**Important Guidelines:**
- Don't use `assume`.
- If the function to be changed is `proof fn`, don't include any `proof {...}` block, just use `assert(...)` directly.
- If a failed post-condition contains a conjunction and we don't know which conjunct is failing, split the conjunction into multiple assertions with each assertion about one conjunct. This helps identify the specific failing conjunct.
- Use `if-else` statements to handle different cases, instead of using `match` statements with `_` patterns.

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
