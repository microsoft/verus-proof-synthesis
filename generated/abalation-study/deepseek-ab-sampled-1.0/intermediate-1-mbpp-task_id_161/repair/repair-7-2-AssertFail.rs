
use vstd::prelude::*;

fn main() {}

verus! {
proof fn lemma_vec_remove<T>(vec: Seq<T>, i: int)
    requires
        0 <= i < vec.len(),
    ensures
        forall |k: int| 0 <= k < i ==> #[trigger] vec[k] == vec.remove(i)[k],
        forall |k: int| i < k  < vec.len() ==> #[trigger] vec[k] ==  vec.remove(i)[k-1],
{
    if i < 0 || i >= vec.len() as int {
        return;
    }
    if i == 0 {
        assert(forall |k: int| 0 <= k < i ==> false);
        assert(forall |k: int| i < k  < vec.len() ==> vec[k] ==  vec.remove(i)[k - 1]);
        return;
    }
}

proof fn lemma_vec_push<T>(vec: Seq<T>, i: T, l: usize)
    requires
        l == vec.len(),
    ensures
        forall |k: int| 0 <= k < l ==> #[trigger] vec[k] == vec.push(i)[k],
        vec.push(i).index(l as int) == i,
{
}

#[verifier::loop_isolation(false)]
fn contains(str: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
{
    let mut i = 0;
    while i < str.len() {
        if (str[i] == key) {
            return true;
        }
        i += 1;
    }
    false
}

fn remove_elements(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        forall|i: int|
            0 <= i < result.len() ==> (arr1@.contains(#[trigger] result[i]) && !arr2@.contains(
                #[trigger] result[i],
            )),
        forall|i: int|
            0 <= i < arr1.len() ==> (arr2@.contains(#[trigger] arr1[i]) || result@.contains(#[trigger] arr1[i])),
{
    let mut output_str = Vec::new();
    let mut index: usize = 0;

    invariant
        forall |k: int| 0 <= k < output_str.len() ==> !arr2@.contains(output_str[k]),
        forall |k: int| 0 <= k < index ==> (arr2@.contains(arr1[k as int]) || output_str@.contains(arr1[k as int])),
        0 <= index <= arr1.len(),
        output_str.len() <= index;

    while index < arr1.len() {
        if !contains(arr2, arr1[index]) {
            let old_len = output_str.len();
            output_str.push(arr1[index]);
            proof {
                lemma_vec_push(output_str @, arr1[index as int], old_len);
                assert(output_str.len() == old_len + 1);
                assert(output_str[old_len as int] == arr1[index as int]);
            }
        }
        index += 1;
    }

    proof {
        assert(forall |i: int| 0 <= i < arr1.len() =>
                (arr2@.contains(#[trigger] arr1[i]) || output_str@.contains(#[trigger] arr1[i])));
    }

    output_str
}

proof fn lemma_seq_subrange_ascend<T>(v: Seq<T>, i: int, j: int)
    requires
        0 <= i < j <= v.len(),
    ensures
        v.subrange(i as int, j as int).drop_last() == v.subrange(i as int, j as int - 1 ),
{
    assert(v.subrange(i as int, j as int).drop_last() =~= v.subrange(i as int, j as int - 1));
}

proof fn lemma_seq_subrange_all<T>(v: Seq<T>)
    ensures
        v == v.subrange(0, v.len() as int),
{
    assert(v =~= v.subrange(0, v.len() as int));
}
}


//         assert(forall |i: int| 0 <= i < arr1.len() ==> (arr2@.contains(arr1[i]) || output_str@.contains(arr1[i])));
//   assertion failed: forall |i: int| 0 <= i < arr1.len() ==> (arr2@.contains(arr1[i]) || output_str@.contains(arr1[i]))

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False