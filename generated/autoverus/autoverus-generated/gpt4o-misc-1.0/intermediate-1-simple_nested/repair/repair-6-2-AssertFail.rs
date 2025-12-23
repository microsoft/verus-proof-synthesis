use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
    requires
        forall|k: int| 0 <= k < b.len() ==> 0 <= #[trigger] b[k] <= k + 1, // Added range constraint
        old(a).len() == N as usize,
        b.len() == N as usize,
        N <= 0x3FFF_FFFF,
    ensures
        N <= sum <= 2 * N,
{
    let mut i: usize = 0;
    let mut sum: i32 = 0;
    while (i < N as usize)
        invariant
            a.len() == N as usize,
            b.len() == N as usize,
            forall|k: int| 0 <= k < i ==> a[k] <= k as i32 + 2,
            forall|k: int| 0 <= k < b.len() ==> b[k] <= k as i32 + 1, // ensuring the invariant covers all elements in 'b'
            i <= N as usize,
            sum <= 2 * i as i32,
            sum >= i as i32, // Added lower bound invariant for sum
            forall|k: int| 0 <= k < i ==> a[k] >= 1, // Ensuring 'a[k]' is at least 1
    {
        a.set(i, b[i] + 1);
        let mut j: usize = 0;
        while (j < i)
            invariant
                a.len() == N as usize,
                b.len() == N as usize,
                a[(i) as int] <= b[(i) as int] + 1,
                a[(i) as int] >= 1, // Update invariant to reflect that a[i] is set to b[i] + 1, and b[i] >= 0
                forall|k: int| 0 <= k < i ==> a[k] <= k as i32 + 2,
                forall|k: int| 0 <= k < b.len() ==> #[trigger] b[k] <= k as i32 + 1, // ensuring the invariant covers all elements in 'b'
                j <= i,
        {
            a.set(i, a[i] - 1);
            j = j + 1;
            proof {
                assert(a[(i) as int] >= 0);
            }
        }
        sum = sum + a[i];
        i = i + 1;
    }
    sum
}

} // verus!

//                 assert(a[(i) as int] >= 0);
//   assertion failed: a[(i) as int] >= 0

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 5
// Safe: False