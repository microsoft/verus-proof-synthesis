
let s1 = Seq::new(N, |i: int| b[i] + 1);
assert(s1.len() == N);
assert(s1.index(k) <= k + 1);
assert(k <= N - 1);



//         sum = sum + a[i];
// failed precondition
//         i < vec.view().len(),
//   failed precondition: i < vec.view().len()
//   None: a[i]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False