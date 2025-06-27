
use vstd::prelude::*;
fn main() {}
verus! {
    #[verifier::loop_isolation(false)]
    fn concat(a: &Vec<u64>, b: &Vec<u64>) -> (c: Vec<u64>)
        requires
            a.len() <= 100 && b.len() <= 100,
        ensures
            c@.len() == a@.len() + b@.len(),
            forall|i: int| 
                (0 <= i && i < a.len()) ==> c[i] == a[i],
                forall|i: int| 
                (a.len() <= i && i < c.len()) ==> c[i] == b[i - a.len()],
    {
        let mut c = Vec::with_capacity(a.len() + b.len());
        let mut n: usize = 0;
        let len: usize = a.len() + b.len();
        while n != len
            invariant
                a.len() <= 100,
                b.len() <= 100,
                forall|i: int|
                    (0 <= i && i < n) ==> (
                        (0 <= i && i < a.len() && c[i] == a[i]) || 
                        (a.len() <= i && i < c.len() && c[i] == b[i - a.len()])
                    ),
                n <= a.len() + b.len(),
            {
            c.push(
                if 0 <= n && n < a.len() {
                    a[n]
                } else {
                    b[n - a.len()]
                },
            );
            n = n + 1;
            assert(
                forall|i: int| 
                (0 <= i && i < n) ==> (
                    (0 <= i && i < a.len() && c[i] == a[i]) || 
                    (a.len() <= i && i < c.len() && c[i] == b[i - a.len()])
                )
            ); // Added by AI, for assertion fail
            assert(
                (0 <= n && n <= len) ==> (
                    (0 <= n && n <= a.len() && c[n - 1] == a[n - 1]) ||
                    (a.len() <= n && n <= len && c[n - 1] == b[n - a.len() - 1])
                )
            ); // Added by AI, for assertion fail
        }
        c
    }
} // verus!


//                 forall|i: int| 
//                 (0 <= i && i < n) ==> (
//                     (0 <= i && i < a.len() && c[i] == a[i]) || 
//                     (a.len() <= i && i < c.len() && c[i] == b[i - a.len()])
//                 )
//   assertion failed: forall|i: int|                  (0 <= i && i < n) ==> (                     (0 <= i && i < a.len() && c[i] == a[i]) ||                      (a.len() <= i && i < c.len() && c[i] == b[i - a.len()])                 )

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 3
// Safe: True