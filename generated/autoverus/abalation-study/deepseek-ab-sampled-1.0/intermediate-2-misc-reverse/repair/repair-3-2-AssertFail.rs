
use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

fn reverse(v: &mut Vec<u64>)
    ensures
        v.len() == old(v).len(),
        forall|i: int| 0 <= i < old(v).len() ==> v[i] == old(v)[old(v).len() - i - 1],
{
    let length = v.len();
    let mut n: usize = 0;
    while n < length / 2
        invariant
            0 <= n <= length / 2,
            forall|i: int| 0 <= i < n as int ==> v[i] == old(v)[length as int - i - 1],
            forall|i: int| n as int <= i < (length - n) as int ==> v[i] == old(v)[i as int],
            makes forts {
                "Elements before n are swapped" => 0 <= i < n as int ==> v[i] == old(v)[length as int - i - 1],
                "Elements between n and length - n remain the same" => n as int <= i < (length - n) as int ==> v[i] == old(v)[i as int]
            }
    {
        let x = v[n];
        let y = v[length - 1 - n];
        v.set(n, y);
        v.set(length - 1 - n, x);
        n = n + 1;
    }
    proof {
        // Ensure that the loop has completed for all necessary iterations
        assert(n == length / 2);
        // Introduce a lemma to help with the final proof
        lemma_for_loop_completion(v, length, n);
    }
}

lemma_for_loop_completion(v: &mut Vec<u64>, length: usize, n: usize)
    requires
        n == length / 2,
        forall<i: int> 0 <= i < n as int ==> v[i] == old(v)[length as int - i - 1],
        forall<i: int> n as int <= i < (length - n) as int ==> v[i] == old(v)[i as int],
{
    // Use completes to handle the transition after the loop
    completes;
    // Expect the final assertion to hold based on the loop invariants
    expects forall|i: int| 0 <= i < length as int ==> v[i] == old(v)[length as int - i - 1];
}
} // verus!


//         assert(forall|i: int| 0 <= i < old(v).len() ==> v[i] == old(v)[old(v).len() - i - 1]);
//   assertion failed: forall|i: int| 0 <= i < old(v).len() ==> v[i] == old(v)[old(v).len() - i - 1]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False