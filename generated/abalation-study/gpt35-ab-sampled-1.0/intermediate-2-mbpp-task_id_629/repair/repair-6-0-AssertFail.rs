
verus! {

    #[verifier::loop_isolation(false)]
    fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
        ensures
            even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
    {
        reveal(Seq::filter); // Added to help Verus understand filter
        
        let mut even_numbers: Vec<u32> = Vec::new();
        let mut index = 0;
        proof {
            lemma_seq_subrange_all(arr@);  // Adding lemma invocation here
            lemma_seq_subrange_all(arr@);  // Adding lemma invocation here
            assert(even_numbers@ == arr@.subrange(0, 0).filter(|x: u32| x % 2 == 0));
            assert(forall |k: int| 0 <= k < arr.len() ==> arr[k] % 2 == 0);
        } // Moved loop invariant as an assertion
        while index < arr.len()
            invariant
                even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0),
                index <= arr.len(),
        {
            if (arr[index] % 2 == 0) {
                even_numbers.push(arr[index]);
            }
            index += 1;
            proof {
                lemma_seq_subrange_ascend(arr@, 0, index as int);  // Adding lemma invocation here
                lemma_seq_subrange_all(arr@);  // Adding lemma invocation here
                assert(even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0));
            } // Added by AI
        }
        even_numbers
    }
} // verus!


//             assert(even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0));
//   assertion failed: even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0)

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False