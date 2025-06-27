
use vstd::prelude::*;

fn main() {}

verus! {
    #[verifier::loop_isolation(false)]
    fn concat(a: &Vec<u64>, b: &Vec<u64>) -> (c: Vec<u64>)
        requires a.len() <= 100 && b.len() <= 100,
        ensures c@.len() == a@.len() + b@.len(),
                forall|i: int| (0 <= i && i < a.len()) ==> c[i] == a[i],
                forall|i: int| (a.len() <= i && i < c.len()) ==> c[i] == b[i - a.len()]
    {
        assert a.len() <= 100;
        assert b.len() <= 100;
        assert c.len() == a.len() + b.len();
        
        let mut c = Vec::with_capacity(a.len() + b.len());
        let mut n: usize = 0;
        let len: usize = a.len() + b.len();
        while n != len
            invariant
                n <= a.len() + b.len(),
                forall|i: int| (0 <= i && i < n) ==> ((0 <= i && i < a.len() && c[i] == a[i]) || (a.len() <= i && i < c.len() && c[i] == b[i - a.len()]))
        {
            c.push(if n < a.len() { a[n] } else { b[n - a.len()] });
            n = n + 1;
        }
        c
    }
} // verus!


//             c.len() == a.len() + b.len(),
//   None: c.len() == a.len() + b.len()

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False