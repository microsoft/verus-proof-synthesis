
use vstd::prelude::*;
fn main() {}

verus! {

fn check_b_property(b: &Vec<i32>, N: i32) -> bool {
    forall |k: int| 0 <= k < N ==> b[k] <= k + 1
}

fn check_a_property(a: &Vec<i32>, b: &Vec<i32>, N: usize) -> bool {
    forall |k: int| 0 <= k < N as int ==> a[k] == b[k] + (1 - k as i32)
}

pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
    requires
        check_b_property(b, N),
        old(a).len() as i32 == N,
        b.len() as i32 == N,
        N <= 0x3FFF_FFFF,
    ensures
        N <= sum <= 2 * N,
{
    let mut i: usize = 0;
    let mut sum: i32 = 0;
    
    while (i < N as usize)
        invariant
            N <= 0x3FFF_FFFF,
            b.len() as i32 == N,
            a.len() == b.len(),
            i <= N as usize,
            sum + a.sum() == 1 + sum,
       {
        a.set(i, b[i] + 1);
        let mut j: usize = 0;
        while (j < i)
            invariant
                N <= 0x3FFF_FFFF,
                b.len() as i32 == N,
                i <= N as usize,
                a[j as int] == b[j as int] + 1 - j as i32,
                j <= i,
                a.len() == b.len(),
        {
            a.set(i, a[i] - 1);
            j = j + 1;
        }
        sum = sum + a[i];
        i = i + 1;
    }
    sum
}

}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpwvia0oc8`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 7
// Safe: False