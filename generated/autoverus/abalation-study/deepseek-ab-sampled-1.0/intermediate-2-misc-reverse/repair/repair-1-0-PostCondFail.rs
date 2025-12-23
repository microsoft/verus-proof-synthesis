

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
        let old_len = length;
        let mut n: usize = 0;
        while n < length / 2 {
            let x = v[n];
            let y = v[length - 1 - n];
            v.set(n, y);
            v.set(length - 1 - n, x);
            n = n + 1;
        }
        proof {
            let old_v = old(v);
            for i in 0..length as int {
                let j = length - 1 - i as int;
                if i < n as int {
                    assert(old_v[i as int] == v[j as usize]);
                } else {
                    assert(old_v[i as usize] == v[i as usize]);
                }
            }
        }
    }
}


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

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 7
// Safe: False