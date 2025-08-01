
use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

fn reverse(v: &mut Vec<u64>)
    ensures
        v.len() == old(v).len(),
        forall|i: int| 0 <= i < old(v).len() ==> v[i] == old(v)[old(v).len() - i - 1],
{
    let old_v = ghost old(v);
    let length = v.len();
    let mut n: usize = 0;
    while n < length / 2
        invariant
            old_v.len() == length,
            v.len() == length,
            n <= length / 2,
            (n as int) <= length as int,
            forall|i: int| 0 <= i < n ==> v[i] == old_v[length as int - i - 1],
            forall|i: int| (n as int) <= i < (length as int) - n as int ==> v[i] == old_v[i],
    {
        let x = v[n];
        let y = v[length - 1 - n];
        
        proof {
            assert(forall|i: int| 0 <= i < n ==> v[i] == old_v[length as int - i - 1]);
            assert(forall|i: int| n as int <= i < (length as int) - n as int ==> v[i] == old_v[i]);
        }
        
        v.set(n, y);
        v.set(length - 1 - n, x);
        
        proof {
            assert(v[n as int] == old_v[length as int - (n as int) - 1]);
            let n_ghost = ghost n + 1;
            assert(forall|i: int| 0 <= i < (n + 1) as int ==> v[i] == old_v[length as int - i - 1]);
            assert(forall|i: int| (n + 1) as int <= i < (length as int) - (n + 1) as int ==> v[i] == old_v[i]);
        }
        
        n = n + 1;
    }
    proof {
        assert(forall|i: int| 0 <= i < length as int / 2 as int ==> v[i] == old_v[length as int - i - 1]);
        assert(forall|i: int| (length as int / 2 as int) <= i < (length as int) - (length as int / 2 as int) ==> v[i] == old_v[i]);
        assert(length as int - (length as int / 2 as int) == (length as int / 2 as int) + (length as int % 2));
        if length % 2 == 0 {
            assert(forall|i: int| 0 <= i < length as int ==> v[i] == old_v[length as int - i - 1]);
        } else {
            assert(forall|i: int| 0 <= i < length as int ==> v[i] == old_v[length as int - i - 1]);
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
//   at the end of the function body: {     let length = v.len();     let mut n: usize = 0;     while n < length / 2         invariant             old(v).len() == length,             v.len() == length,             n <= length / 2,             (n as int) <= length as int,             forall|i: int| 0 <= i < n ==> v[i] == old(v)[length as int - i - 1],             forall|i: int| (n as int) <= i < (length as int) - n as int ==> v[i] == old(v)[i],     {         let x = v[n];         let y = v[length - 1 - n];                  proof {             assert(forall|i: int| 0 <= i < n ==> v[i] == old(v)[length as int - i - 1]);             assert(forall|i: int| n as int <= i < (length as int) - n as int ==> v[i] == old(v)[i]);         }                  v.set(n, y);         v.set(length - 1 - n, x);         n = n + 1;     }     proof {         let remaining = length as int - 2 * n as int;         assert(forall|i: int| 0 <= i < n as int ==> v[i] == old(v)[length as int - i - 1]);         assert(forall|i: int| n as int <= i < remaining ==> v[i] == old(v)[i]);         assert(length as int - n as int == n as int + remaining);     } }
//   failed this postcondition: forall|i: int| 0 <= i < old(v).len() ==> v[i] == old(v)[old(v).len() - i - 1]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False