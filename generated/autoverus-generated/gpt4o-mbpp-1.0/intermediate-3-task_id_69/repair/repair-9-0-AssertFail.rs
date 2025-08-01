
use vstd::prelude::*;
fn main() {}
verus! {

proof fn lemma_seq_subrange_all<T>(v: Seq<T>)
    ensures
        v == v.subrange(0, v.len() as int),
{
    assert(v =~= v.subrange(0, v.len() as int));
}

proof fn lemma_seq_subrange_ascend<T>(v: Seq<T>, i:int, j: int)
    requires
        0<= i < j <= v.len(),
    ensures
        v.subrange(i, j as int).drop_last() == v.subrange(i, j-1 ),
{
    assert(v.subrange(i, j as int).drop_last() =~= v.subrange(i, j-1));
}

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
            forall|k: int| 0 <= k < i ==> main[idx + k] == sub[k],
            i <= sub.len(),
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
        lemma_seq_subrange_all(main@);
    }
    proof {
        assert(exists|k: int, l: int| 0 <= k <= 0 && l == k + sub.len() && (main@.subrange(k, l)) =~= sub@);
    }
    while index <= (main.len() - sub.len())
        invariant
            exists|k: int, l: int|
                0 <= k <= index && l == k + sub.len() && (# [trigger] (main@.subrange(k, l))) =~= sub@,
            index <= main.len() - sub.len() + 1,
            sub.len() <= main.len(),
            main.len() == main.len(),
            sub.len() == sub.len(),
    {
        if (is_sub_list_at_index(&main, &sub, index)) {
            return true;
        }
        proof {
            if index < (main.len() - sub.len()) {
                lemma_seq_subrange_ascend(main@, 0, index as int + 1);
                assert(exists|k: int, l: int| 0 <= k <= index + 1 && l == k + sub.len() && (main@.subrange(k, l)) =~= sub@);
            }
        }
        index += 1;
    }
    false
}

} // verus!


//         assert(exists|k: int, l: int| 0 <= k <= 0 && l == k + sub.len() && (main@.subrange(k, l)) =~= sub@);
//   assertion failed: exists|k: int, l: int| 0 <= k <= 0 && l == k + sub.len() && (main@.subrange(k, l)) =~= sub@

// Compilation Error: False, Verified: 4, Errors: 1, Verus Errors: 2
// Safe: True