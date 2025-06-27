use vstd::prelude::*;

fn main() {}

verus! {

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
            0 <= idx,
            idx <= main.len() - sub.len(),
            i <= sub.len(),
            idx + i <= main.len(),
            main@.len() == main.len(),
            sub@.len() == sub.len(),
            forall |j: int|
                0 <= j < i ==> main[idx + j] == sub[j],
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
            sub.len() <= main.len(),
            0 <= index <= (main.len() - sub.len() + 1),
            main@.len() == main.len(),
            sub@.len() == sub.len(),
            forall |k: int, l: int|
                0 <= k < index && l == k + sub.len()
                ==> !(main@.subrange(k, l) =~= sub@),
    {
        if (is_sub_list_at_index(&main, &sub, index)) {
            return true;
        }
        index += 1;
    }
    false
}
} // verus!
// Score: (4, 0)
// Safe: True