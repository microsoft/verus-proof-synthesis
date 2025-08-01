
use vstd::prelude::*;
fn main() {}

verus! {
fn reverse(v: &mut Vec<u64>)
    ensures
        v.len() == old(v).len(),
        forall |i: int| 0 <= i < old(v).len() ==> v[i] == old(v)[old(v).len() - i - 1],
{
    let old_v = old(v);
    let old_len = old_v.len();

    let mut n: usize = 0;
    while n < old_len / 2 {
        invariant
            n <= old_len / 2,
            0 <= n <= old_len,
            old_len < 1000,
            // Invariant: For each 0 <= i < n, v[i] == old_v[old_len - i - 1]
            forall |i: int| 0 <= i < n as int ==> v[i] == old_v[old_len - i - 1 as usize],
            // Invariant: For each old_len - n <= i < old_len, v[i] == old_v[old_len - i - 1]
            forall |i: int| (old_len - n as int) <= i < old_len as int ==> v[i] == old_v[old_len - i - 1 as usize],
        {
            let front = n as int;
            let back = old_len - n as int - 1;
            assert(0 <= front < old_len);
            assert(0 <= back < old_len);

            // Swap elements at front and back positions
            let temp = v[front as usize];
            v.set(front as usize, v[back as usize]);
            v.set(back as usize, temp);

            proof {
                // Ensure the swap didn't affect other parts of the vector
                let unchanged = |i: int| {
                    if i < n as int || i >= old_len - n as int {
                        v[i] == old_v[i]
                    } else {
                        true
                    }
                };

                assert(forall |i: int| 0 <= i < old_len as int ==> unchanged(i));
            }

            n = n + 1;
        }
    }
}
}

// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1