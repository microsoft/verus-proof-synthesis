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
            // Comment: The array `sub` is not modified in the loop
            forall|j: int| 0 <= j < sub.len() ==> sub[j as int] == sub[j as int],
            i <= sub.len(),
            sub.len() <= main.len(),
            main.len() == main.len(),
            sub.len() == sub.len(),
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
        assert(exists|k: int, l: int| 0 <= k < index ==> k + sub.len() == l && (main@.subrange(k, l) =~= sub@));
    } // Added by AI
    while index <= (main.len() - sub.len())
        invariant
            exists|k: int, l: int|
                0 <= k < index ==> k + sub.len() == l && (main@.subrange(k, l) =~= sub@),
            // Comment: The array `sub` is not modified in the loop
            forall|j: int| 0 <= j < sub.len() ==> sub[j as int] == sub[j as int],
            index <= main.len() - sub.len(),
            sub.len() <= main.len(),
            main.len() == main.len(),
            sub.len() == sub.len(),
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
//                 0 <= k < index ==> k + sub.len() == l && (main@.subrange(k, l) =~= sub@),
//   None: exists|k: int, l: int|                 0 <= k < index ==> k + sub.len() == l && (main@.subrange(k, l) =~= sub@)

// Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 4
// Safe: True