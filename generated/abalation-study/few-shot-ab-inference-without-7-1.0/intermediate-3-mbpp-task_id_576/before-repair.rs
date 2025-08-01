
use vstd::prelude::*;
fn main() {}
verus! {

fn sub_array_at_index(main: &Vec<i32>, sub: &Vec<i32>, idx: usize) -> (result: bool)
    requires
        sub.len() <= main.len(),
        0 <= idx <= (main.len() - sub.len()),
    ensures
        result == (main@.subrange(idx as int, (idx + sub@.len())) =~= sub@),
{
    let mut i = 0;
    while i < sub.len()
        invariant
            0 <= i <= sub.len(),
            0 <= idx <= (main.len() - sub.len()),
            forall|j: int| 0 <= j < i as int ==> main[idx + j as usize] == sub[j as int],
            sub.len() <= main.len(),
            0 <= idx <= (main.len() - sub.len()),
            // Array `main` is not modified in the loop
            forall|k: int| 0 <= k < main.len() ==> main[k] == main[k], 
            // Array `sub` is not modified in the loop
            forall|k: int| 0 <= k < sub.len() ==> sub[k] == sub[k],    
    {
        if (main[idx + i] != sub[i]) {
            return false;
        }
        i += 1;
    }
    true
}

fn is_sub_array(main: &Vec<i32>, sub: &Vec<i32>) -> (result: bool)
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
    while index <= (main.len() - sub.len())
        invariant
            0 <= index <= (main.len() - sub.len() + 1),
            exists|k: int, l: int|
                0 <= k < index as int && l == k + sub.len() && (# [trigger] (main@.subrange(k, l)))
                    =~= sub@,
            sub.len() <= main.len(),
            // Array `main` is not modified in the loop
            forall|k: int| 0 <= k < main.len() ==> main[k] == main[k], 
            // Array `sub` is not modified in the loop
            forall|k: int| 0 <= k < sub.len() ==> sub[k] == sub[k],
            main.len() == main.len(),
            sub.len() == sub.len(),
    {
        if (sub_array_at_index(&main, &sub, index)) {
            return true;
        }
        index += 1;
    }
    false
}

} // verus!

// Score: Compilation Error: False, Verified: 3, Errors: 1, Verus Errors: 2