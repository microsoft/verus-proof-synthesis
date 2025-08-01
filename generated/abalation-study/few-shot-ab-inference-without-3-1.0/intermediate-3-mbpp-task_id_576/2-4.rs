use vstd::prelude::*;

fn main() {}

verus! {

fn sub_array_at_index(main: &Vec<i32>, sub: &Vec<i32>, idx: usize) -> (result: bool)
    requires
        sub.len() <= main.len(),
        0 <= idx <= (main.len() - sub.len()),
    ensures
        result == (main@.subrange(idx as int, idx as int + sub@.len()) =~= sub@),
{
    let mut i = 0;
    while i < sub.len()
        invariant
            i <= sub.len(),
            result == (i == sub.len() ==> (main@.subrange(idx as int, idx as int + sub@.len()) =~= sub@)),
            forall |j: usize| 0 <= j < i ==> main[idx + j] == sub[j],
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
            0 <= k <= (main.len() - sub.len()) && l == k + sub.len() && (#[trigger] (main@.subrange(
                k,
                l,
            ))) =~= sub@),
{
    if sub.len() > main.len() {
        return false;
    }
    let mut index = 0;
    while index <= (main.len() - sub.len())
        invariant
            index <= main.len() - sub.len() + 1,
            result == (exists|k: int, l: int|
                0 <= k < index && l == k + sub.len() && (#[trigger] (main@.subrange(
                    k,
                    l,
                ))) =~= sub@),
    {
        if (sub_array_at_index(&main, &sub, index)) {
            return true;
        }
        index += 1;
    }
    false
}

} // verus!
// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2