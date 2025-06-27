
    #[verifier::loop_isolation(false)]
    fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
        ensures
            even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
    {
        reveal(Seq::filter);
        let index = 5; // For example
        lemma_seq_subrange_all(arr@);
        let result = arr.filter(|x: u32| x % 2 == 0);
        lemma_seq_subrange_ascend(arr@, 0, index as int + 1);
        lemma_seq_subrange_all(arr@.subrange(0, index as int));
        assert(arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0) == even_numbers@);
        result
    }
    // ... rest of the verus block


//                 assert(arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0) == even_numbers@);
//   assertion failed: arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0) == even_numbers@

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False