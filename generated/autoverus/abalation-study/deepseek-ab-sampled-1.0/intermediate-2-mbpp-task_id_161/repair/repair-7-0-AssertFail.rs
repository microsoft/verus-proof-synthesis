
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
        }
        index += 1;
        proof {
            lemma_vec_push(output_str@, arr1[( index - 1 ) as int], output_str.len() - 1);
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


//             assert(forall|j: int| 0 <= j < index ==> (arr2@.contains(# [trigger] arr1[j]) || output_str@.contains(# [trigger] arr1[j])));
//   assertion failed: forall|j: int| 0 <= j < index ==> (arr2@.contains(# [trigger] arr1[j]) || output_str@.contains(# [trigger] arr1[j]))

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False