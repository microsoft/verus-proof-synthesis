
use vstd::seq::*;

#[verifier::loop_isolation(false)]
pub fn myfun(a: &mut Seq<i32>, b: &mut Seq<i32>, c: &mut Seq<i32>, sum: &mut Seq<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(b).len() == N,
        old(c).len() == N,
        old(sum).len() == 1,
        N < 1000,
    ensures
        sum[0] <= 3 * N,
{
    sum.set(0, 0);
    let mut i: i32 = 0;
    while (i < N)
        invariant
            a.len() == N,
            i >= 0,
            i <= N,
            sum[0] <= 3 * N,
            N > 0,
            old(a).len() == N,
            old(b).len() == N,
            old(c).len() == N,
            old(sum).len() == 1,
            N < 1000,
    {
        a.set(i as usize, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N)
        invariant
            a.len() == N,
            i >= 0,
            i <= N,
            sum.len() == 1,
            sum[0] <= 3 * N,
            N > 0,
            old(a).len() == N,
            old(b).len() == N,
            old(c).len() == N,
            old(sum).len() == 1,
            N < 1000,
    {
        sum.set(0, sum[0] + a.index(i as usize));
        i = i + 1;
    }
    i = 0;
    while (i < N)
        invariant
            b.len() == N,
            i >= 0,
            i <= N,
            sum.len() == 1,
            sum[0] <= 3 * N,
            N > 0,
            old(a).len() == N,
            old(b).len() == N,
            old(c).len() == N,
            old(sum).len() == 1,
            N < 1000,
    {
        b.set(i as usize, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N)
        invariant
            b.len() == N,
            i >= 0,
            i <= N,
            sum.len() == 1,
            sum[0] <= 3 * N,
            N > 0,
            old(a).len() == N,
            old(b).len() == N,
            old(c).len() == N,
            old(sum).len() == 1,
            N < 1000,
    {
        sum.set(0, sum[0] + b.index(i as usize));
        i = i + 1;
    }
    i = 0;
    while (i < N)
        invariant
            c.len() == N,
            i >= 0,
            i <= N,
            sum.len() == 1,
            sum[0] <= 3 * N,
            N > 0,
            old(a).len() == N,
            old(b).len() == N,
            old(c).len() == N,
            old(sum).len() == 1,
            N < 1000,
    {
        c.set(i as usize, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N)
        invariant
            c.len() == N,
            i >= 0,
            i <= N,
            sum.len() == 1,
            sum[0] <= 3 * N,
            N > 0,
            old(a).len() == N,
            old(b).len() == N,
            old(c).len() == N,
            old(sum).len() == 1,
            N < 1000,
    {
        sum.set(0, sum[0] + c.index(i as usize));
        i = i + 1;
    }
}


//         sum.set(0, sum[0] + c[i]);
// failed precondition
//         i < vec.view().len(),
//   failed precondition: i < vec.view().len()
//   None: sum[0]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False