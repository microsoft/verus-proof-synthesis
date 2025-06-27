use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

fn is_sub_list_at_index(main: &Vec<i32>, sub: &Vec<i32>, idx: usize) -> (result: bool)
    requires
        sub.len() <= main.len(),
        0 <= idx <= (main.len() - sub.len()),
    ensures
        result == (main@.subrange(idx as int, (idx + sub@.len())) =~= sub@),
{
    let mut i = 0;
    while i < sub.len()
        invariant
            0 <= idx <= (main.len() - sub.len()),
            forall|j: int| 0 <= j < i ==> main[idx + j as usize] == sub[j as int],
            i <= sub.len(),
            sub.len() <= main.len(),
            forall|k: int| 0 <= k < main.len() ==> main[k] == main[k], // main is never modified in the loop
            forall|k: int| 0 <= k < sub.len() ==> sub[k] == sub[k],   // sub is never modified in the loop
    {
        if (main[idx + i] != sub[i]) {
            return false;
        }
        i += 1;
    }
    true
}

fn is_sub_list(main: &Vec<i32>, sub: &Vec<i32>) -> (result: bool)
    requires
        sub.len() <= main.len(),
    ensures
        result == (exists|k: int, l: int|
            0 <= k <= (main.len() - sub.len()) && l == k + sub.len() && (# [trigger] (
            main@.subrange(k, l))) =~= sub@),
{
    if sub.len() > main.len() {
        return false;
    }
    let mut index = 0;
    proof {
        assert(exists|k: int, l: int| 0 <= k < index && l == k + sub.len() && (main@.subrange(k, l)) =~= sub@);
    } // Added by AI
    while index <= (main.len() - sub.len())
        invariant
            exists|k: int, l: int|
                0 <= k < index && l == k + sub.len() && (main@.subrange(k, l)) =~= sub@,
            index <= (main.len() - sub.len()) + 1,
            sub.len() <= main.len(),
            forall|k: int| 0 <= k < main.len() ==> main[k] == main[k], // main is never modified in the loop
            forall|k: int| 0 <= k < sub.len() ==> sub[k] == sub[k],   // sub is never modified in the loop
    {
        if (is_sub_list_at_index(&main, &sub, index)) {
            return true;
        }
        index += 1;
    }
    false
}

} // verus!

//             exists|k: int, l: int|
//                 0 <= k < index && l == k + sub.len() && (main@.subrange(k, l)) =~= sub@,
//   None: exists|k: int, l: int|                 0 <= k < index && l == k + sub.len() && (main@.subrange(k, l)) =~= sub@

// Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 1
// Safe: True