use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
    requires
        forall|k: int| 0 <= k < b.len() ==> 1 <= #[trigger] b[k] <= k + 1, // Ensuring boundaries for b[k]
        old(a).len() == N,
        b.len() == N,
        N <= 0x3FFF_FFFF,
    ensures
        N <= sum <= 2 * N,
{
    let mut i: usize = 0;
    let mut sum: i32 = 0;
    while (i < N as usize)
        invariant
            a.len() == N,
            b.len() == N,
            forall|k: int| 0 <= k < i ==> a[k] <= k + 2,
            forall|k: int| 0 <= k < b.len() ==> #[trigger] b[k] <= k + 1, // Ensuring the invariant covers all elements in 'b'
            i <= N as usize,
            sum <= 2 * i as i32,
            b.len() == N,
            N <= 0x3FFF_FFFF,
            sum >= i as i32, // Added lower bound invariant for sum
            forall|k: int| 0 <= k < i ==> a[k] >= 1, // Ensuring 'a[k]' is at least 1
            sum + (i + 1) <= 2 * (i + 1) as i32, // Ensures that the update to sum with a[i] stays within bounds
            a[( i ) as int] >= 1, // Added invariant to ensure a[i] is always at least 1
    {
        a.set(i, b[i] + 1);
        let mut j: usize = 0;
        while (j < i)
            invariant
                a.len() == N,
                a[( i ) as int] <= b[( i ) as int] + 1,
                a[( i ) as int] >= 1, // Added invariant to ensure a[i] is always at least 1
                forall|k: int| 0 <= k < i ==> a[k] <= k + 2,
                forall|k: int| 0 <= k < b.len() ==> #[trigger] b[k] <= k + 1, // Ensuring the invariant covers all elements in 'b'
                j <= i,
                b.len() == N,
                N <= 0x3FFF_FFFF,
        {
            a.set(i, a[i] - 1);
            j = j + 1;
            proof {
                assert(a[(i) as int] >= 1); // Updated assertion to ensure a[i] is always at least 1
            }
        }
        sum = sum + a[i];
        i = i + 1;
    }
    sum
}

} // verus!





//                 assert(a[(i) as int] >= 1); // Updated assertion to ensure a[i] is always at least 1
//   assertion failed: a[(i) as int] >= 1

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 5
// Safe: False