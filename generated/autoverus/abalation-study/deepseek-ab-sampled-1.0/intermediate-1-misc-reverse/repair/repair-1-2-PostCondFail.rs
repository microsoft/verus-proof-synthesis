
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
    let ghost reversed_count = length;
    while n < length / 2
        invariant
            let mid = if length % 2 == 0 { 0 } else { 1 };
            n <= length,
            length == old(v).len(),
            v.len() == length,
            forall|j: int| (0 <= j < n as int) ==> v[j] == old(v)[length - j - 1],
            forall|j: int| (j >= n as int && j < (length - n) as int) ==> v[j] == old(v)[j],
            2 * n + mid <= length,
    {
        let x = v[n];
        let y = v[length - 1 - n];
        v.set(n, y);
        v.set(length - 1 - n, x);
        n = n + 1;
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
//   at the end of the function body: {     let length = v.len();     let mut n: usize = 0;     while n < length / 2         invariant             forall|j: int| (0 <= j < n as int) ==> v[j] == old(v)[length - j - 1],             forall|j: int| (j >= n as int && j < length as int - n as int) ==> v[j] == old(v)[j],             n <= length,             length == old(v).len(),             v.len() == length,     {         let x = v[n];         let y = v[length - 1 - n];         v.set(n, y);         v.set(length - 1 - n, x);         n = n + 1;     } }
//   failed this postcondition: forall|i: int| 0 <= i < old(v).len() ==> v[i] == old(v)[old(v).len() - i - 1]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False