
proof {
    lemma_vec_push(output_str@, arr1[index], output_str.len());
}
if (!contains(arr2, arr1[index])) {
    output_str.push(arr1[index]);
}
proof {
    lemma_vec_remove(arr1@, index);
}
index += 1;


//             assert(forall|i: int| 0 <= i < index ==> (arr2@.contains(# [trigger] arr1[i]) || output_str@.contains(
//                     # [trigger] arr1[i],
//                 )));
//   assertion failed: forall|i: int| 0 <= i < index ==> (arr2@.contains(# [trigger] arr1[i]) || output_str@.contains(                     # [trigger] arr1[i],                 ))

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False