use vstd::prelude::*;

fn main() {}
verus! {

fn append(v: &Vec<u64>, elem: u64) -> (c: Vec<u64>)
    requires
        v.len() <= 100,
    ensures
        c@.len() == v@.len() + 1,
        forall|i: int| (0 <= i && i < v.len()) ==> c[i as int] == v[i as int],
        c@.last() == elem,
{
    let mut c = Vec::with_capacity(v.len() + 1);
    let mut n: usize = 0;
    let len: usize = v.len();
    
    while n != len
        invariant
            0 <= n as int <= len as int,
            c@.len() == n as int,
            forall|i: int| (0 <= i && i < n as int) ==> c[i] == v[i],
            v.len() <= 100,
    {
        c.push(v[n]);
        n = n + 1;
    }
    
    c.push(elem);
    
    c
}

} // verus!



// is safe: False
// Score: Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 1