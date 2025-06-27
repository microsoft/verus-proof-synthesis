
use vstd::prelude::*;
fn main() {}

verus!{
     
spec fn triangle(n: nat) -> nat
    decreases n
{
    if n == 0 {
        0
    } else {
        n + triangle((n - 1) as nat)
    }
}

proof fn lemma_triangle_sum(n: u32, idx: u32)
    requires
        idx <= n,
        triangle(n as nat) < 0x1_0000_0000,
    ensures
        triangle(idx as nat) + idx < 0x1_0000_0000,
{
    // Prove by induction on idx
    if idx == 0 {
        // Base case: when idx is 0, sum is 0 and 0 + 0 = 0 < 0x1_0000_0000
        assert(triangle(0 as nat) == 0);
        assert(0 + 0 < 0x1_0000_0000);
    } else {
        // Inductive step: assume the lemma holds for idx-1, prove for idx
        lemma_triangle_sum(n, ( idx - 1 ) as u32);
        assert(triangle(idx as nat) == triangle((idx - 1) as nat) + idx as nat);
        assert(triangle(idx as nat) < 0x1_0000_0000);
        assert(triangle(idx as nat) + idx < 0x1_0000_0000);
    }
}

fn tail_triangle(n: u32, idx: u32, sum: &mut u32)
    requires
        idx <= n,
        *old(sum) == triangle(idx as nat),
        triangle(n as nat) < 0x1_0000_0000,
    ensures
        *sum == triangle(n as nat),
{
    if idx < n {
        let idx = idx + 1;
        assert(*sum + idx < 0x1_0000_0000) by {
            lemma_triangle_sum(n, idx);
        }
        *sum = *sum + idx;
        tail_triangle(n, idx, sum);
    }
}
}



//         assert(forall |i: int| 0 <= i < arr1.len() ==> (arr2@.contains(arr1[i]) || output_str@.contains(arr1[i])));
//   assertion failed: forall |i: int| 0 <= i < arr1.len() ==> (arr2@.contains(arr1[i]) || output_str@.contains(arr1[i]))

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False