
// ... (other code remains unchanged)

// Assertion with invocation to lemma functions
assert(even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0));
invocation { seq_subrange_ascend(arr, 0, index as nat); }
invocation { seq_subrange_all(arr, 0, index as nat, |x: u32| x % 2 == 0); }



//             assert(even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0));
//   assertion failed: even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0)

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False