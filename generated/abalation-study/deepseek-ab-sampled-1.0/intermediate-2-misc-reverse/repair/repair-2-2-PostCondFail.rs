

use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

fn reverse(v: &mut Vec<u64>)
    ensures
        v.len() == old(v).len(),
        forall|i: int| 0 <= i < old(v).len() ==> v[i] == old(v)[old(v).len() - i - 1],
{
    let length = v.len();
    let mut n: usize = 0;
    while n < length / 2
        invariant
            0 <= n <= length / 2,
            forall|i: int| 0 <= i < n ==> v[i] == old(v)[length - i - 1],
            forall|i: int| 0 <= i < n ==> v[i]@ == old(v)[length - 1 - i as int],
            forall|i: int| n <= i < length - n ==> v[i] == old(v)[i],
            n <= length,
            n <= length / 2,
            v.len() == length,
            v.len() == old(v).len(),
    {
        let x = v[n];
        let y = v[length - 1 - n];
        v.set(n, y);
        v.set(length - 1 - n, x);
        n = n + 1;
    }
    proof {
        assert(forall|i: int| 0 <= i < old(v).len() ==> v[i] == old(v)[old(v).len() - i - 1]);
    }
}

} // verus!

// failed this postcondition
//         forall|i: int| 0 <= i < old(v).len() ==> v[i] == old(v)[old(v).len() - i - 1],
// at the end of the function body
// {
//     let length = v.len();
//     let mut n: usize = 0;
//     while n < length / 2
// ...
//     }
// }
//   at the end of the function body: {     let length = v.len();     let mut n: usize = 0;     while n < length / 2         invariant             0 <= n <= length / 2,             forall|i: int| 0 <= i < n ==> v[i] == old(v)[length - i - 1],             forall|i: int| 0 <= i < n ==> v[i]@ == old(v)[length - 1 - i as int],             forall|i: int| n <= i < length - n ==> v[i] == old(v)[i],             n <= length,             n <= length / 2,             v.len() == length,             v.len() == old(v).len(),     {         let x = v[n];         let y = v[length - 1 - n];         v.set(n, y);         v.set(length - 1 - n, x);         n = n + 1;     } }
//   failed this postcondition: forall|i: int| 0 <= i < old(v).len() ==> v[i] == old(v)[old(v).len() - i - 1]

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1
// Safe: True