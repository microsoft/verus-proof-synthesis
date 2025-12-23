
use vstd::prelude::*;

fn main() {}
verus! {

proof fn concat_index_a(a: &Vec<u64>, b: &Vec<u64>, c: &Vec<u64>, i: usize)
    requires
        a.len() <= 100 && b.len() <= 100 && c.len() == a.len() + b.len() && i < a.len(),
    ensures
        c[( i ) as int] == a[( i ) as int],
    {
        assert!(c[i] == a[i]);
    }

proof fn concat_index_b(a: &Vec<u64>, b: &Vec<u64>, c: &Vec<u64>, i: usize)
    requires
        a.len() <= 100 && b.len() <= 100 && c.len() == a.len() + b.len() && i >= a.len(),
    ensures
        c[( i ) as int] == b[i - a.len()],
    {
        assert!(c[i] == b[i - a.len()]);
    }

fn concat(a: &Vec<u64>, b: &Vec<u64>) -> (c: Vec<u64>)
    requires
        a.len() <= 100 && b.len() <= 100,
    ensures
        c@.len() == a@.len() + b@.len(),
        forall|i: int| (0 <= i && i < a.len()) ==> c[i] == a[i],
        forall|i: int| (a.len() <= i && i < c.len()) ==> c[i] == b[i - a.len()],
{
    let mut c = Vec::with_capacity(a.len() + b.len());
    let mut n: usize = 0;
    let len: usize = a.len() + b.len();
    while n != len
        invariant
            a.len() <= 100,
            b.len() <= 100,
            c.len() == a.len() + b.len(),
            n <= len,
            forall |i:int| 0<= i < n ==> (c[i] == a[i] || c[i] == b[i - a.len()]),
    {
        c.push(
            if 0 <= n && n < a.len() {
                a[n]
            } else {
                b[n - a.len()]
            },
        );
        n = n + 1;

        proof {
            if n-1 < a.len() {
                concat_index_a(a, b, &c, ( n-1 ) as usize);
            } else {
                concat_index_b(a, b, &c, ( n-1 ) as usize);
            }
        }
    }
    c
}

} // verus!






// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1