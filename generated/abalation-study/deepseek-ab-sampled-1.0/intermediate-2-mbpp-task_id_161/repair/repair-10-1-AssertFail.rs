
use vstd::prelude::*;

fn main() {}

verus! {
proof fn lemma_vec_remove<T>(vec: Seq<T>, i: int)
    requires
        0 <= i < vec.len(),
    ensures
        forall |k: int| 0 <= k < i ==> #[trigger] vec[k] == vec.remove(i)[k],
        forall |k: int| i < k < vec.len() ==> #[trigger] vec[k] == vec.remove(i)[k-1],
{
    induction i;
}

proof fn lemma_vec_push<T>(vec: Seq<T>, i: T, l: usize)
    requires
        l == vec.len(),
    ensures
        forall |k: int| 0 <= k < vec.len() ==> #[trigger] vec[k] == vec.push(i)[k],
        vec.push(i).index(l as int) == i,
{
    induction l;
    case l == 0 {
        simp[Seq::push, Seq::index, Seq::len]
    }
    case l > 0 {
        simp[Seq::push, Seq::index, Seq::len]
        split;
    }
}

#[verifier::loop_isolation(false)]

fn contains(str: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
{
    let mut i = 0;
    while i < str.len()
        invariant
            0 <= i <= str.len(),
            str.len() >= 0,
            str.len() == str@.len(),
    {
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
            0 <= i < result.len() ==> (arr1@.contains(# [trigger] result[i]) && !arr2@.contains(
                # [trigger] result[i],
            )),
        forall|i: int|
            0 <= i < arr1.len() ==> (arr2@.contains(# [trigger] arr1[i]) || result@.contains(
                # [trigger] arr1[i],
            )),
{
    let mut output_str = Vec::new();
    let mut index: usize = 0;
    while index < arr1.len()
        invariant
            forall|j: int|
                0 <= j < index ==> (arr2@.contains(# [trigger] arr1[j]) || output_str@.contains(
                    # [trigger] arr1[j],
                )),
            forall|j: int|
                0 <= j < output_str.len() ==> (arr1@.contains(# [trigger] output_str[j])
                    && !arr2@.contains(# [trigger] output_str[j])),
            index <= arr1.len(),
            output_str.len() <= index,
            index <= arr1.len(),
            output_str.len() <= arr1.len(),
            arr1.len() == arr1@.len(),
            arr2.len() == arr2@.len(),
    {
        if (!contains(arr2, arr1[index])) {
            output_str.push(arr1[index]);
            proof {
                lemma_vec_push(output_str@, arr1[index as int], output_str.len());
                assert(output_str@.push(arr1[index as int]).index(output_str.len() as int) == arr1[index as int]);
                assert(output_str@.push(arr1[index as int]).contains(arr1[index as int]));
                assert(forall|j: int|
                    0 <= j < output_str.len()
                    ==>
                    arr1@.contains(# [trigger] output_str@.push(arr1[index as int])[j as int])
                    && !arr2@.contains(# [trigger] output_str@.push(arr1[index as int])[j as int]));
            }
        }
        index += 1;
        proof {
            lemma_vec_push(output_str@, arr1[( index ) as int], output_str.len());
            assert(forall|j: int| 0 <= j < index ==> (arr2@.contains(# [trigger] arr1[j]) || output_str@.contains(# [trigger] arr1[j])));
            assert(forall|j: int| 0 <= j < output_str.len() ==> (arr1@.contains(# [trigger] output_str[j]) && !arr2@.contains(# [trigger] output_str[j])));
            assert(index <= arr1.len());
            assert(output_str.len() <= index);
            assert(index <= arr1.len());
            assert(output_str.len() <= arr1.len());
            assert(arr1.len() == arr1@.len());
            assert(arr2.len() == arr2@.len());
        }
    }
    output_str
}
}


//             assert(forall|j: int| 0 <= j < index ==> (arr2@.contains(# [trigger] arr1[j]) || output_str@.contains(# [trigger] arr1[j])));
//   assertion failed: forall|j: int| 0 <= j < index ==> (arr2@.contains(# [trigger] arr1[j]) || output_str@.contains(# [trigger] arr1[j]))

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False