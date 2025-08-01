
verus! {
    #[verifier::loop_isolation(false)]
    pub fn myfun(a: &mut Vec<usize>, sum: &mut Vec<usize>, N: usize)
        requires
            old(a).len() == N,
            old(sum).len() == 1,
            N > 0,
        ensures
            sum[0] <= N,
    {
        let mut i: usize = 0;
        while (i < N as usize)
            invariant
                a.len() == N,
                i <= N,
        {
            a.set(i, i % 2);
            i = i + 1;
        }
        i = 0;
        while (i < N as usize)
            invariant
                forall|j: int| 1 <= j <= i ==> sum[j - 1] + a[j] >= 0,
                i <= N,
                sum.len() == 1,
                i >= 0,
        {
            if (i == 0) {
                sum.set(0, 0);
            } else {
                sum.set(0, sum[0] + a[i]);
            }
            i = i + 1;
        }
    }
}


//                 sum.set(0, sum[0] + a[i]);
// failed precondition
//         i < vec.view().len(),
//   failed precondition: i < vec.view().len()
//   None: sum[0]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False