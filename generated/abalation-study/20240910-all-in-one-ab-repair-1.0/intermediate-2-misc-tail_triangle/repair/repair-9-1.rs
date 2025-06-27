
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_isolation(false)] // Attribute added for fine-grained loop verification control

    spec fn triangle(n: nat) -> nat
        decreases n,
    {
        if n == 0 {
            0
        } else {
            n + triangle((n - 1) as nat)
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
            let new_idx = idx + 1;
            *sum = *sum + new_idx;
            tail_triangle(n, new_idx, sum);
        }
    }
}

fn main() {
    let mut sum: u32 = 0;
    tail_triangle(5, 0, &mut sum);
    println!("Triangle number: {}", sum);
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpy65ghldx`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False