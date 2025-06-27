use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
    requires
        forall|k: int| k <= # [trigger] b[k] <= k + 1,
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
            a.len() == N as usize,
            b.len() == N as usize,
            forall|k: int| k < i as int ==> 1 <= a[#[trigger] k as int],  
            i <= N as usize,
            sum <= 2 * i, // Ensuring 'sum' doesn't overflow by associating it with 'i'.
            sum >= i, // Ensuring 'sum' doesn't underflow by associating it with 'i', assuming minimum value added each time is 1.
    {
        a.set(i, b[i] + 1);
        let mut j: usize = 0;
        while (j < i)
            invariant
                a.len() == N as usize,
                b.len() == N as usize, // Added for completeness: even though b is not modified, it is accessed by b[i] in the outer loop.
                i <= N as usize,
                j <= i,
                // This invariant does not need to be changed to the forall form since a.set() is called within the loop.
        {
            a.set(i, a[i] - 1);
            j = j + 1;
        }
        // Assert added to ensure 'sum + a[i]' does not cause overflow/underflow
        assert(sum + a[( i ) as int] <= 2 * N); // Adding boundary condition based on function's post-condition
        assert(sum + a[( i ) as int] >= 0);     // Ensuring the sum doesn't underflow
        sum = sum + a[i];
        i = i + 1;
    }
    sum
}

} // verus!



//             forall|k: int| k < i ==> 1 <= a[k], // Because a is being modified in this loop through a.set(), this invariant remains unchanged.
//   None: forall|k: int| k < i ==> 1 <= a[k]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: True