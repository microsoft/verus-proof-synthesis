
fn find_dissimilar(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>) {
  ...
  // Before the first loop
  assert(forall|i: int| 0 <= i < result.len() ==> (!arr2@.contains(#[trigger] result[i])));
  
  let mut index = 0;
  while index < arr1.len()
      invariant
          0 <= index <= arr1.len(),
          forall|i: int| 0 <= i < result.len() ==> (!arr2@.contains(#[trigger] result[i])),
  {
      ...
  }

  // Before the second loop
  assert(forall|i: int| 0 <= i < result.len() ==> (!arr1@.contains(#[trigger] result[i])));

  index = 0;
  while index < arr2.len()
      invariant
          0 <= index <= arr2.len(),
          forall|i: int| 0 <= i < result.len() ==> (!arr1@.contains(#[trigger] result[i])),
  {
      ...
  }
  ...
}


//             forall|i: int| 0 <= i < result.len() ==> (!arr1@.contains(#[trigger] result[i])),
//   None: forall|i: int| 0 <= i < result.len() ==> (!arr1@.contains(#[trigger] result[i]))

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False