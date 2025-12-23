Your mission is to address the failing assertion by turning the current lemma into a proof by induction.

## Step 1: Analyze where induction is needed

Analyze the lemma and relevant definitions to determine where it will be necessary to apply induction.
Here are some common scenarios when induction is necessary:
- Proving facts about natural numbers which can simplify to facts about smaller numbers
- Proving facts about recursive spec fns

In the example below, we see that the spec fn `seq_filter` is recursive. This suggests that we may need induction to prove the given lemma about `seq_filter` and `len`.

```rust
pub open spec fn seq_filter<A>(s: Seq<A>, pred: spec_fn(A) -> bool) -> Seq<A>
    decreases s.len(),
{
    if s.len() == 0 {
        s
    } else {
        let subseq = seq_filter(s.drop_last(), pred);
        if pred(s.last()) {
            subseq.push(s.last())
        } else {
            subseq
        }
    }
}

pub proof fn seq_filter_len<A>(s: Seq<A>, pred: spec_fn(A) -> bool)
    ensures
        seq_filter(s, pred).len() <= s.len(),
{
    assert(seq_filter(s, pred).len() <= s.len());
}
```

## Step 2: Identify base case(s)

Identify what case(s) do not require inductive invocations of the lemma. These will be the base cases.

In the `seq_filter_len` example, we see that the base case will be when `s.len() == 0`. This is because when the length of the sequence is `0`, the expression `seq_filter(s, pred)` will simplify to `s`, and this does not contain any more instances of `seq_filter`.

## Step 3: Identify inductive case(s) and inductive hypotheses

Now identify what case(s) will require induction. Furthermore, determine what *inductive hypotheses* will be needed to prove the lemma. These will become the inductive invocations of the lemma. Recall that an inductive hypothesis can be invoked on a parameter that you make "smaller".

In the `seq_filter_len` example, we examine the definition of `seq_filter` to see that the recursive invocation is called with the arguments `seq_filter(s.drop_last(), pred)`. Therefore, an inductive invocation of the lemma `seq_filter_len(s.drop_last(), pred)` allows us to prove that `seq_filter(s.drop_last(), pred).len() <= s.drop_last().len()`. This fact will allow us to later prove the desired conclusion of the lemma, because `seq_filter(s, pred)` will simplify to either `seq_filter(s.drop_last(), pred)` or `seq_filter(s.drop_last(), pred).push(s.last())`.

**IMPORTANT:** Make sure to assert the target property this induction is meant to prove in BOTH the case case and
the inductive case.

In the `seq_filter_len` example below, we include the assert `assert(seq_filter(s, pred).len() <= s.len());` at the
end of both the base case and the inductive case.


## Step 4: Add decreases clause

Verus requires us to explicitly prove that recursive/inductive functions terminate.
We do this by supplying a `decreases` clause in the lemma definition which states an expression on the function arguments that decreases to 0 with each inductive invocation of the lemma.

**IMPORTANT:** there are two things a `decreases` clause must satisfy:
- Its value must decrease on all recursive calls/inductive invocations.
- Its value must not go below 0 (even if there is a minimum value).

Here are some example `decreases` clauses:
- `decreases n` for a single number `n`
- `decreases c.len()` for some collection `c`
- `decreases x - y` for some numbers `x`, `y` for which `x` grows towards `y`

**IMPORTANT:** a `decreases` clause HAS to be put AFTER the requires AND the ensures clause of the recursive function!!!
**IMPORTANT:** a `decreases` clause HAS to be put AFTER the requires AND the ensures clause of the recursive function!!!

In the `seq_filter_len` example, the decreases clause will simply be `decreases s.len()`, since the length of the sequence argument will decrease with the inductive invocation `seq_filter_len(s.drop_last(), pred)` that we identified above.

## Guidelines

- Insert into the lemma case analysis branches for each base and inductive case.
- Use good style by replacing isolated failing assertions using an `assert(...) by {}` block.
- In each branch for a base case:
  - Add assertion(s) for the failing assertion within the branch.
  - **Do not add any extra assertions or do further simplification, just perform direct substitution.** You will have the opportunity to further develop the proof for each case in subsequent debugging steps.
- In each branch for an inductive case:
  - Insert the appropriate inductive invocation of the lemma.
  - Add assertion(s) for the failing assertion within the branch.
  - **Do not add any extra assertions or do further simplification, just perform direct substitution.**
- Add a `decreases` clause after the `ensures` clause on the lemma to help Verus prove termination.

Example:
Before:
```rust
pub open spec fn seq_filter<A>(s: Seq<A>, pred: spec_fn(A) -> bool) -> Seq<A>
    decreases s.len(),
{
    if s.len() == 0 {
        s
    } else {
        let subseq = seq_filter(s.drop_last(), pred);
        if pred(s.last()) {
            subseq.push(s.last())
        } else {
            subseq
        }
    }
}

pub proof fn seq_filter_len<A>(s: Seq<A>, pred: spec_fn(A) -> bool)
    ensures
        seq_filter(s, pred).len() <= s.len(),
{
    assert(seq_filter(s, pred).len() <= s.len()); // FAILS
}
```

```rust
<<<<<<< SEARCH
    ensures
        seq_filter(s, pred).len() <= s.len(),
=======
    ensures
        seq_filter(s, pred).len() <= s.len(),
    decreases
        s.len()
>>>>>>> REPLACE

<<<<<<< SEARCH
assert(seq_filter(s, pred).len() <= s.len());
=======
assert(seq_filter(s, pred).len() <= s.len()) by {
    if (s.len() == 0) {
        // copy outer assertion to branch
        assert(seq_filter(s, pred).len() <= s.len());
    } else {
        // invoke lemma inductively
        let subseq = seq_filter(s.drop_last(), pred);
        seq_filter_len(s.drop_last(), pred);
        // copy outer assertion to branch
        assert(seq_filter(s, pred).len() <= s.len());
    }
}
>>>>>>> REPLACE
```
