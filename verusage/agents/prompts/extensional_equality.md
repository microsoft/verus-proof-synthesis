Your mission is to fix the assertion error using extensional equality, i.e., by proving collection equality via element-wise equality.

## When to Apply Extensional Equality

Use this repair strategy when:
- The assertion involves collection equality (`seq1 =~= seq2`, `map1 =~= map2`, `set1 =~= set2`, or `struct1 == struct2` where one or more of the fields of the struct is a collection)
- The way to establish that those collections are equal is to show that corresponding elements are equal

## Core Principle: Length/Domain First, Then Elements

**CRITICAL**: Always establish length/domain/cardinality equality FIRST, then prove element-wise equality.

1. **Sequences**: `seq1.len() == seq2.len()`, then `∀i. 0 ≤ i < seq1.len() ⟹ seq1[i] =~= seq2[i]`
2. **Maps**: `map1.dom() =~= map2.dom()`, then `∀k. map1.dom().contains(k) ⟹ map1[k] =~= map2[k]`
3. **Sets**: `∀x. set1.contains(x) ⟹ set2.contains(x)` and `∀x. set2.contains(x) ⟹ set1.contains(x)` (no length equality needed)

## Step 1: Identify collection equality patterns
- Analyze the failing assertion for collection equality or properties needing element-wise reasoning
- Determine the collection type: `Seq<T>`, `Map<K,V>`, `Set<T>`, or nested structures
- Determine nesting level: simple collections, nested collections, or deeply nested structures

## Step 2: Transform to extensional equality
- Apply the appropriate strategy, which depends on what type of collection it is
- **For sequences, always start with length equality assertion; for maps, always start with domain equality assertion**
- Then add element-wise equality quantified assertion
- Use good style by replacing isolated failing assertions with `assert(...) by {}` blocks
- **Do not add extra complex reasoning, just directly transform the assertion according to the strategy**

### Pattern for Sequences

Example 1 - Basic sequence equality:

Before:
```rust
fn test(seq1: Seq<u8>, seq2: Seq<u8>) {
    assert(seq1 == seq2);
}
```

Change:
```rust
<<<<<<< SEARCH
    assert(seq1 == seq2);
=======
    assert(seq1 =~= seq2) by {
        // Step 1: Establish length equality FIRST
        assert(seq1.len() == seq2.len());
        // Step 2: Prove element-wise equality
        assert forall |i: int| 0 <= i < seq1.len() implies seq1[i] =~= seq2[i] by {
            assert(seq1[i] =~= seq2[i]);
        };
    }
>>>>>>> REPLACE
```

Example 2 - Nested sequences (Seq<Seq<T>>):

Before:
```rust
fn test(matrix1: Seq<Seq<u8>>, matrix2: Seq<Seq<u8>>) {
    assert(matrix1 == matrix2);
}
```

Change:
```rust
<<<<<<< SEARCH
    assert(matrix1 == matrix2);
=======
    assert(matrix1 =~= matrix2) by {
        // Step 1: Establish outer length equality
        assert(matrix1.len() == matrix2.len());
        // Step 2: Prove row-wise equality
        assert forall |i: int| 0 <= i < matrix1.len() implies matrix1[i] =~= matrix2[i] by {
            // Step 2a: Establish inner length equality for each row
            assert(matrix1[i].len() == matrix2[i].len());
            // Step 2b: Prove element-wise equality within each row
            assert forall |j: int| 0 <= j < matrix1[i].len() implies matrix1[i][j] =~= matrix2[i][j] by {
                assert(matrix1[i][j] =~= matrix2[i][j]);
            };
        };
    }
>>>>>>> REPLACE
```

### Pattern for Maps

Example 3 - Map equality:

Before:
```rust
fn test(map1: Map<int, String>, map2: Map<int, String>) {
    assert(map1 == map2);
}
```

Change:
```rust
<<<<<<< SEARCH
    assert(map1 == map2);
=======
    assert(map1 =~= map2) by {
        // Step 1: Establish domain equality FIRST
        assert(map1.dom() =~= map2.dom());
        // Step 2: Prove value equality for all keys in domain
        assert forall |k: int| map1.dom().contains(k) implies map1[k] =~= map2[k] by {
            assert(map1[k] =~= map2[k]);
        };
    }
>>>>>>> REPLACE
```

Example 4 - Nested map with sequence values:

Before:
```rust
fn test(map1: Map<int, Seq<u8>>, map2: Map<int, Seq<u8>>) {
    assert(map1 == map2);
}
```

Change:
```rust
<<<<<<< SEARCH
    assert(map1 == map2);
=======
    assert(map1 =~= map2) by {
        // Step 1: Establish domain equality
        assert(map1.dom() =~= map2.dom());
        // Step 2: Prove sequence equality for each key
        assert forall |k: int| map1.dom().contains(k) implies map1[k] =~= map2[k] by {
            // Step 2a: Establish sequence length equality
            assert(map1[k].len() == map2[k].len());
            // Step 2b: Prove element-wise equality within sequences
            assert forall |i: int| 0 <= i < map1[k].len() implies map1[k][i] =~= map2[k][i] by {
                assert(map1[k][i] =~= map2[k][i]);
            };
        };
    }
>>>>>>> REPLACE
```

### Pattern for Sets

Example 5 - Set equality:

Before:
```rust
fn test(set1: Set<u8>, set2: Set<u8>) {
    assert(set1 == set2);
}
```

Change:
```rust
<<<<<<< SEARCH
    assert(set1 == set2);
=======
    assert(set1 =~= set2) by {
        // Step 1: Prove bidirectional containment: forward direction
        assert forall |x: u8| set1.contains(x) implies set2.contains(x) by {
            assert(set2.contains(x));
        };
        // Step 2: Prove bidirectional containment: reverse direction
        assert forall |x: u8| set2.contains(x) implies set1.contains(x) by {
            assert(set1.contains(x));
        };
    }
>>>>>>> REPLACE
```

## Step 3: Handle conditional collection equality

For conditional assertions involving collections:

Before:
```rust
if condition {
    assert(seq1 == seq2);
}
```

Change:
```rust
<<<<<<< SEARCH
if condition {
    assert(seq1 == seq2);
}
=======
if condition {
    assert(seq1 =~= seq2) by {
        // Step 1: Establish length equality under condition
        assert(seq1.len() == seq2.len());
        // Step 2: Prove element-wise equality
        assert forall |i: int| 0 <= i < seq1.len() implies seq1[i] =~= seq2[i] by {
            assert(seq1[i] =~= seq2[i]);
        };
    }
}
>>>>>>> REPLACE
```

## Step 4: General pattern for arbitrary nesting

For collections with arbitrary nesting depth:
1. **Start from the outermost level** and work inward
2. **Establish length/domain equality at each level** before proving element equality
3. **Use distinct variable names** for each level (`i`, `j`, `k`, etc.)
4. **Nest the quantified assertions** to match the nesting structure

## Important Notes:

- **ALWAYS establish length/domain equality FIRST** - this is crucial for extensional equality
- **Use proper bounds** in quantifier conditions:
  - Sequences: `0 <= i < seq.len()`
  - Maps: `map.dom().contains(k)`
- **Use `implies` instead of `==>` when introducing universal quantifiers*** (`assert forall |x| P(x) implies Q(x) by { ... }`)
- **Use `=~=` for the comparison of collections**
- **Proof blocks should be empty** - assert only the consequent of the `implies` statement. **Do not add any extra assertions or do further simplification, just perform direct substitution.** You will have the opportunity to further develop the proof for each case in subsequent debugging steps.
- **Don't inline complex operations** - preserve the original structure
- **Use descriptive comments** to clarify which level of nesting each quantifier addresses

## Summary of Patterns:

| Collection Type | Length/Domain | Element Equality |
|----------------|---------------|------------------|
| `Seq<T>` | `seq1.len() == seq2.len()` | `forall \|i\| 0 <= i < seq1.len() implies seq1[i] =~= seq2[i]` |
| `Map<K,V>` | `map1.dom() =~= map2.dom()` | `forall \|k\| map1.dom().contains(k) implies map1[k] =~= map2[k]` |
| `Set<T>` | None | `forall \|x\| set1.contains(x) implies set2.contains(x)` and `forall \|x\| set2.contains(x) implies set1.contains(x)` |

**Remember**: Length/domain equality first, then element equality! Please use `=~=` for the comparison of collections.
