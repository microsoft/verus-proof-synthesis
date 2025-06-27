The failure of the invariant to hold at the beginning of the loop can be a subtle issue to tackle, particularly if the loop's logic and invariants are correctly capturing the intended behavior but aren't properly initiated. Given your description, let's consider what's happening around the point of the issue:

1. The loop invariant that fails is meant to ensure that all elements in the `result` vector at any point before or during the execution of the loop are not contained in `arr1`. However, for this invariant to hold at the beginning of the loop, we must be sure that `result` is initially in a state that satisfies this condition.

2. Before each loop starts, `result` is empty. Thus, it trivially satisfies the invariant because there are no elements in `result` that could violate the condition of not being contained in `arr1` or `arr2`. But, this assumption must be either correctly stated or properly transitioned into the loop invariants and checked by the verification tool.

3. Looking at the loop that processes `arr1` and aims to fill `result` with elements not present in `arr2` and not already included in `result`, and similarly for the loop that processes `arr2`, we need to ensure that we're correctly setting up the assumptions for these checks.

Given these points, the code provided seems logically consistent with what you're aiming to achieve, and the specified invariants look correct for the stated purpose. However, the verification engine's issue with the invariant not holding at the start might be due to how it interprets the initialization state of `result` and requires an explicit assertion or a clearer initialization state that guarantees the invariant's condition.

To correct or satisfy the failing invariant before the loop regarding `result` and `arr1`, you can assert right before the loop starts that `result` satisfies the condition of the invariant. While typically unnecessary due to how Rust and Verus work with vector initialization, explicitly asserting the empty state of `result` aligns with loop invariant expectations could help. Unfortunately, Verus syntax for direct assertions outside of function preconditions, postconditions, or loop invariants isn't directly supported as in some other verification systems. Instead, ensuring correct initial conditions typically involves structuring function preconditions or loop invariants effectively.

To proceed within the typical use and restrictions of Verus, ensuring the loop invariant holds at the beginning can be more about ensuring the logic explicitly supports this—something that seems to already be the case given `result` starts empty and is only added to under conditions that should ensure the invariants.

Since Verus currently does not support assertions in the same way some other verifiers might (e.g., directly asserting a state immediately before a loop), and given `result` is correctly initialized empty, it appears the aforementioned invariants should be correct from the start, ensuring no discrepancies.

Given this, if the verifier struggles with this part, reexamining the tool's version or its documentation for any updates or quirks is wise. Another step could be breaking down the invariants or adding detailed comments to guide the verifier, although these approaches move away from direct code changes.

//             forall|i: int| 0 <= i < result.len() ==> (!arr1@.contains(#[trigger] result[i])),
//   None: forall|i: int| 0 <= i < result.len() ==> (!arr1@.contains(#[trigger] result[i]))

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 50
// Safe: False