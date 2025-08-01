

use vstd::prelude::*;

fn main() {}

verus! {
proof fn lemma_contains(str: Seq<i32>, key: i32)
    requires
        true,
    ensures
        !str.contains(key) ==> !str.to_set().contains(key),
        str.contains(key) ==> str.to_set().contains(key),
{
    assert(str.contains(key) <==> str.to_set().contains(key));
}

proof fn lemma_remove_elements_correctness(arr1: Seq<i32>, arr2: Seq<i32>, output_str: Seq<i32>)
    requires
        true,
    ensures
        forall |i: int| 0 <= i < arr1.len() ==> (arr2.contains(arr1[i]) || output_str.contains(arr1[i])),
{
    assert(forall |i: int| 0 <= i < arr1.len() ==> (arr2.contains(arr1[i]) || output_str.contains(arr1[i])));
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
            0 <= i < arr1.len() ==> (arr2@.contains(#[trigger] arr1[i]) || result@.contains(
                #[trigger] arr1[i],
            )),
{
    let mut output_str = Vec::new();
    let mut index: usize = 0;

    while index < arr1.len()
        invariant
            forall |k: int| 0 <= k < output_str.len() ==> !arr2@.contains(output_str[k]),
            0 <= index <= arr1.len(),
            output_str.len() <= index,
    {
        if (!contains(arr2, arr1[index])) {
            output_str.push(arr1[index]);
            proof {
                lemma_vec_push(output_str @, arr1[( index ) as int], output_str.len());
            }
        }
        index += 1;
    }

    proof {
        lemma_contains(arr1@, *arr1[index as int]);
        lemma_remove_elements_correctness(arr1@, arr2@, output_str@);
        assert(forall |i: int| 0 <= i < arr1.len() ==> (arr2@.contains(arr1[i]) || output_str@.contains(arr1[i])));
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
// Safe: True