Your mission is to help prove the failing assertion by adding a new inductive lemma to the current file. You will be given guidance on what the lemma should state. Your task is to correctly create a lemma stub with appropriate pre- and post-conditions which can be fully proven in subsequent debugging steps.

## Step 1: Analyze where induction is needed

Analyze the current lemma, the failing assertion, and relevant definitions to determine where it will be necessary to factor out a lemma which requires induction.
Here are some common scenarios when induction is necessary:
- Proving facts about natural numbers which can simplify to facts about smaller numbers
- Proving facts about recursive spec fns

Here is an example: in `seq_filter_len` below, the failing assertion could be proven if we had a proof about `seq_filter` and `seq_add` which stated that `seq_filter(seq_add(s1, s2), pred) =~= seq_add(seq_filter(s1, pred), seq_filter(s2, pred))`. Such a proof would require induction since it is about recursive spec functions `seq_filter` and `seq_add`.

```rust
pub open spec fn seq_filter<A>(s: Seq<A>, pred: spec_fn(A) -> bool) -> Seq<A>
    decreases s.len(),
{
    if (s =~= Seq::empty()) {
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

pub open spec fn seq_add<A>(s1: Seq<A>, s2: Seq<A>) -> Seq<A>
    decreases s2.len()
{
    if (s2 =~= Seq::empty()) {
        s1
    } else {
        seq_add(s1, s2.drop_last()).push(s2.last())
    }
}

pub proof fn seq_filter_len<A>(s1: Seq<A>, s2: Seq<A>, pred: spec_fn(A) -> bool)
    ensures
        seq_filter(s2, pred) =~= Seq::empty() ==> seq_filter(s1, pred) =~= seq_filter(seq_add(s1, s2), pred),
{
    if (seq_filter(s2, pred) =~= Seq::empty()) {
        assert(seq_filter(s1, pred) =~= seq_filter(seq_add(s1, s2), pred)); // FAILS
    }
}
```

## Step 2: Determine pre- and postconditions

Determine the signature for the new helper lemma by its pre- and postconditions. Make sure to consider:
- What postcondition(s) are necessary to prove the failing assertion
- What preconditions are necessary to prove the postcondition
- What facts are true at the call-site of the helper lemma in the original proof and whether the preconditions would be satisfied

In the above example, we determined that the desired postcondition is `seq_filter(seq_add(s1, s2), pred) =~= seq_add(seq_filter(s1, pred), seq_filter(s2, pred))`. Since this fact should always be true, the proof fn will not have any preconditions. Thus the signature of the lemma will look like this:

```rust
pub proof fn seq_filter_add<A>(s1: Seq<A>, s2: Seq<A>, pred: spec_fn(A) -> bool)
    ensures
        seq_filter(seq_add(s1, s2), pred) =~= seq_add(seq_filter(s1, pred), seq_filter(s2, pred))
{
}
```

## Step 3: Optional: Add `decreases` clause

Verus requires us to explicitly prove that recursive/inductive functions terminate.
We do this by supplying a `decreases` clause in the lemma definition which states an expression on the function arguments that decreases to 0 with each inductive invocation of the lemma.

If the decreasing expression for the new helper lemma is already known, then add it to the function signature. If the decreasing argument is not yet known, you may skip this step.

**IMPORTANT:** there are two things a `decreases` clause must satisfy:
- Its value must decrease on all recursive calls/inductive invocations.
- Its value must not go below 0 (even if there is a minimum value).

Here are some example `decreases` clauses:
- `decreases n` for a single number `n`
- `decreases c.len()` for some collection `c`
- `decreases x - y` for some numbers `x`, `y` for which `x` grows towards `y`

In the above example, the decreases clause will be `decreases s2.len()`, since both `seq_add` recurses on the second argument.  Thus the updated signature of the lemma is as follows:

```rust
pub proof fn seq_filter_add<A>(s1: Seq<A>, s2: Seq<A>, pred: spec_fn(A) -> bool)
    ensures
        seq_filter(seq_add(s1, s2), pred) =~= seq_add(seq_filter(s1, pred), seq_filter(s2, pred))
    decreases
        s2.len() // NEW
{
}
```

## Step 4: Leave lemma body blank

In the body of the new lemma, simply add an assertion for the postcondition. This will act as a stub for further debugging later.

Finishing the above example, the final helper lemma stub should look like this:

```rust
pub proof fn seq_filter_add<A>(s1: Seq<A>, s2: Seq<A>, pred: spec_fn(A) -> bool)
    ensures
        seq_filter(seq_add(s1, s2), pred) =~= seq_add(seq_filter(s1, pred), seq_filter(s2, pred))
    decreases
        s2.len()
{
    assert(seq_filter(seq_add(s1, s2), pred) =~= seq_add(seq_filter(s1, pred), seq_filter(s2, pred))); // to debug further
}
```

## Guidelines
- Analyze the code in the file to determine why induction is necessary to prove the failing assertion.
- Determine the exact pre- and postconditions necessary to prove the failing assertion.
- If the decreasing expression is already known, add a `decreases` clause after the `ensures` clause on the lemma to help Verus prove termination.
