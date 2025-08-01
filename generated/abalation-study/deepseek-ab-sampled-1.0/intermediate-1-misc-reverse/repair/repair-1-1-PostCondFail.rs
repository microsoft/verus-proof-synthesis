

use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

fn reverse(v: &mut Vec<u64>)
    ensures
        v.len() == old(v).len(),
        forall|i: int| 0 <= i < old(v).len() ==> v[i] == old(v)[old(v).len() - i - 1],
{
    let ghost old_v: Seq<u64> = old(v); // Added by AI
    let ghost len_old = old_v.len(); // Added by AI

    let length = v.len();
    let mut n: usize = 0;
    while n < length / 2
        invariant
            forall|j: int| (0 <= j < n as int) ==> v[j] == old_v[length - j - 1],
            forall|j: int| (j >= n as int && j < length as int - n as int) ==> v[j] == old_v[j],
            n <= length,
            length == old_v.len(),
            v.len() == length,
    {
        let x = v[n];
        let y = v[length - 1 - n];
        v.set(n, y);
        v.set(length - 1 - n, x);
        n = n + 1;
    }
    proof {
        for (i in 0..len_old) {
            assert(v[i] == old_v[len_old - i - 1]);
        }
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
//   at the end of the function body: {     let length = v.len();     let mut n: usize = 0;     while n < length / 2         invariant             forall|j: int| (0 <= j < n as int) ==> v[j] == old(v)[length - j - 1],             forall|j: int| (j >= n as int && j < length as int - n as int) ==> v[j] == old(v)[j],             n <= length,             length == old(v).len(),             v.len() == length,     {         let x = v[n];         let y = v[length - 1 - n];         v.set(n, y);         v.set(length - 1 - n, x);         n = n + 1;     } }
//   failed this postcondition: forall|i: int| 0 <= i < old(v).len() ==> v[i] == old(v)[old(v).len() - i - 1]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False