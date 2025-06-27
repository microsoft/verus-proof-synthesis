
#[verifier::seq_subrange_all]
fn lemma_seq_subrange_all<T>(s: &Seq<T>)
    ensures s@ == s[..] // Add this line
{}

#[verifier::loop_isolation(false)]

fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
    requires
        lemma_seq_subrange_all(arr@),  // Add this line
        lemma_seq_subrange_ascend(arr@, 0, index as int),  // Add this line
    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
    {
        reveal(Seq::filter); // Add this line
        // ... rest of your function
    }


//                 assert(arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0) == even_numbers@);
//   assertion failed: arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0) == even_numbers@

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False