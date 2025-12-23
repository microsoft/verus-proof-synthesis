# Add Trigger Assert Action

Your mission is to help the Verus verifier prove a failed assertion by preceding it with another assertion that triggers the instantiation of one or more quantified formulas.

## Understanding Triggers in Verus

Verus uses **triggers** to control when quantified formulas (forall/exists) are instantiated. The verifier only uses a `forall` quantified formula when it encounters a term that matches the formula's trigger pattern. Without proper triggering, the verifier cannot make use of such quantified knowledge.

**Key Principle**: Suppose you have `forall |x: T| #[trigger] P(x) ==> Q(x)` where `P(x)` and `Q(x)` are arbitrary expressions involving the universally quantified variable `x`. If you want the verifier to know `Q(y)`, you need to assert something that contains `P(y)` to trigger the instantiation.

## Target Code Analysis

The code you need to fix will have error lines marked with:
```
// VERUS_ERROR_HERE
```

Focus your analysis on the failed assertion and its surrounding context.

## Step-by-Step Repair Process

### Step 1: IDENTIFY THE FAILED ASSERTION
- Locate the assertion that's failing (marked with the error comment)
- Understand what the assertion is trying to prove
- Identify what knowledge the verifier needs to establish this assertion

### Step 2: COMPREHENSIVE TRIGGER PATTERN DISCOVERY
Systematically search for ALL relevant trigger patterns in these locations (in order of priority):

**A. Function Preconditions (`requires` clauses)**
- Look for quantified expressions with `#[trigger]` annotations
- Example: `requires forall |i| 0 <= i < len ==> #[trigger] array[i] > 0`
- Trigger pattern: `array[i]`

**B. Previous Assertions in the Same Function**
- Check all `assert` statements before the failed one
- Look for quantified assertions with triggers
- Example: `assert(forall |k| valid_index(k) ==> #[trigger] data[k].is_valid());`
- Trigger pattern: `data[k].is_valid()`

**C. Spec Function Bodies** (if referenced in preconditions or previous assertions)
- If a spec function is used, examine its body for trigger patterns
- Recursively check nested spec function calls
- Example: If `valid_range(arr)` is used, check its definition for triggers

**D. Loop Invariants** (if inside a loop)
- Check invariant clauses for quantified expressions with triggers

**CRITICAL**: Do NOT use trigger patterns from the currently failing assertion itself. Only use patterns from OTHER sources listed above.

### Step 3: TRIGGER MATCHING ANALYSIS
For each trigger pattern found:

1. **Pattern Structure**: Identify the exact form of the trigger
   - Example: `#[trigger] pm_regions_view[i].committed()` has pattern `pm_regions_view[?].committed()`

2. **Required Instantiation**: Determine what values need to be substituted
   - Example: If you need to prove something about index `j`, you need `pm_regions_view[j].committed()`

3. **Gap Analysis**: Check if matching expressions already exist in the current context
   - If missing, you need to add trigger assertions

### Step 4: ADD STRATEGIC TRIGGER ASSERTIONS
Add an assertion that matches the missing trigger pattern.

**Practical Examples:**

1. **Simple Trigger***
```rust
// If you need to trigger: `forall |i| 0 <= i < len ==> #[trigger] arr[i] > 0`
// and you want to prove something about arr[j]:
assert(arr[j] > 0);  // This triggers the quantified knowledge for index j
```

2. **Universally Quantifying a Variable to Use it in a Trigger:***
```rust
// If you need to trigger: `forall |k| #[trigger] valid(k) ==> data[k].property()`
// and you want to use it to prove something about a set of values of `k`,
// introduce a variable with a universal quantifier, then use it in a trigger,
// as in:
assert forall |k| 0 <= k < size implies data[k].property() by {
    // This assertion triggers the quantified formula for every k satisfying `0 <= k < size`:
    assert(valid(k));
}
```

3. **Universally Quantifying Multiple Variables to Use in Triggers:***
```rust
// If you have: `forall |x, y| #[trigger] p(x, y) ==> q(x, y)` and
// you want to instantiate it for a set of values of the associated
// variables, introduce them with a universal quantifier, as in:
assert forall |x, y| #[trigger] q(x, y) by {
    assert(p(x, y));
}

// You can also do this with nested quantifier introductions, as in:
assert forall |x| r(x) by {
    assert forall |y| q(x, y) by {
       assert(p(x, y));
    }
}
```

4. **Chaining Triggers***
```rust
// Sometimes you can instantiate one or more quantifiers with just a single trigger.
// This happens when the instantiation of one quantifier triggers the same or a different
// quantifier. Here's an example:

proof fn lemma_p_implies_q_implies_r(a: int)
    requires
        forall |x| #[trigger] p(x) ==> q(x),
        forall |x| #[trigger] q(x) ==> r(x),
    ensures
        r(a),
{
    // Using `p(a)` triggers the instantiation of the first quantified formula
	// to give `q(a)`, which in turn triggers an instantiation of the second
	// quantified formula to give `r(a)`.
    assert(p(a));
}

// Here's another example:
proof fn lemma_q3()
    requires
        forall|x| #![trigger p(x), q(x)] p(x) && q(x) ==> q(x + 1),
        p(0),
        p(1),
        p(2),
    ensures
        q(3),
{
    // The following assertion triggers the precondition quantifier,
    // instantiating it and learning `q(1)`. This itself triggers the
	// quantifer again to learn `q(2)`. This triggers the quantifier
	// again, to learn `q(3)`. At this point, the chain of triggers
	// stops because there is nothing to trigger `p(3)`.
    assert(q(0));
}
```

### Step 5: VERIFICATION AND REFINEMENT
- Ensure your trigger assertions are logically sound
- Check that they provide the necessary quantifier instantiations to prove the failed assertion
- Add explanatory comments for complex trigger chains

## Common Trigger Patterns

1. **Array/Sequence Access**: `#[trigger] arr[i]`, `#[trigger] seq[k]`
2. **Function Calls**: `#[trigger] f(x)`, `#[trigger] obj.method()`
3. **Field Access**: `#[trigger] struct.field`, `#[trigger] obj.property`
4. **Complex Expressions**: `#[trigger] f(g(x))`, `#[trigger] obj.prop1.prop2`

Note that triggers NEVER involve mathematical operations like `+`, `-`, `*`, or `%`.
So, for instance, `x + 1` CANNOT be a trigger.

## Trigger Strategy Guidelines

1. **Start Simple**: Begin with the most direct trigger expressions needed
2. **Work Backwards**: From the failing assertion, identify what knowledge is missing
3. **Use Quantified Variables**: Sometimes, introduce universally quantified variables to use for triggering
4. **Chain Triggers**: Look for opportunities to do multiple chained instantiations with one trigger
5. **Be Specific**: Target the exact instantiations needed for your proof
6. **Add Comments**: Explain which trigger patterns you're targeting and why

## Important Notes

- **Always** provide logical justification for your trigger assertions
- **Focus** on the specific instantiations needed for the failing assertion
- **Comment** your reasoning to explain the trigger strategy
- **Test** that your additions are syntactically correct Verus code
- **Don't over-trigger**: Only add assertions that are actually needed

## Output Format

Provide the complete modified code with:
1. Clear comments explaining your trigger analysis
2. Strategic trigger assertions added to proof blocks
3. Proper Verus syntax and formatting
4. Logical flow from triggers to the final assertion

**Example Output Structure:**
```rust
assert forall |x| condition(x) implies goal(x) by {
    // Step 1: Trigger pattern from precondition: #[trigger] helper(x)
    assert(helper(x));

    // Step 2: Use triggered knowledge to establish intermediate fact
    assert(intermediate_fact(x));

    // Step 3: Combine facts to prove the goal
    assert(goal(x));
};
```

NEVER use `fix`, `assume`, `intro`, or `show` inside the proof block, as these are not valid in Verus proof blocks.
