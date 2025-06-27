
#[verifier::lemma_call]
lemma_seq_subrange_all(arr@); // Call the lemma function just after initializing even_numbers

//...

proof {
    lemma_seq_subrange_ascend(arr@, 0, index as int); // Call the lemma function inside the proof block
    lemma_seq_subrange_all(arr@);  // Call the lemma function inside the proof block
    assert(even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0));
} // Moved loop invariant as an assertion


//             assert(even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0));
//   assertion failed: even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0)

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False