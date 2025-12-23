
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
            0 <= idx <= (main.len() - sub.len()),
            forall|j: int| 0 <= j < i ==> main[idx + j as usize] == sub[j as int],
            forall |j:int| 0<= j < sub.len() ==> sub[j as int] == sub[j as int], // Because sub is never changed in the loop
            i <= sub.len(),
            sub.len() <= main.len(),
            main.len() == main.len(),
            sub.len() == sub.len(),
            0 <= idx <= (main.len() - sub.len()),  // repeated invariant
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
            0 <= index <= main.len() - sub.len() + 1,
            sub.len() <= main.len(),
            forall |j:int| 0<= j < main.len() ==> main[j as int] == main[j as int], // Because main is never changed in the loop
            forall |j:int| 0<= j < sub.len() ==> sub[j as int] == sub[j as int], // Because sub is never changed in the loop
            main.len() == main.len(),
            sub.len() == sub.len(),
            sub.len() <= main.len(),  // repeated invariant
    {
        if (sub_array_at_index(&main, &sub, index)) {
            return true;
        }
        index += 1;
    }
    false
}

} // verus!

// Score: Compilation Error: False, Verified: 3, Errors: 1, Verus Errors: 1