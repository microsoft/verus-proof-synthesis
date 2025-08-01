
use vstd::prelude::*;
fn main() {}

verus! {
    spec fn filter_odd(seq: Seq<u32>) -> Seq<u32> {
        seq.filter(|x: u32| x % 2 != 0)
    }

    #[verifier::proof]
    fn correct_filter_odd(seq: Seq<u32>) {
        let filtered = filter_odd(seq);
        let expected = seq.filter(|x: u32| x % 2 != 0);
        assert(filtered =~= expected);
    }

    fn find_odd_numbers(arr: &Vec<u32>) -> (odd_numbers: Vec<u32>)
        ensures
            odd_numbers@ == arr@.filter(|x: u32| x % 2 != 0),
    {
        let mut odd_numbers: Vec<u32> = Vec::new();
        let input_len = arr.len();
        let mut index = 0;

        while index < arr.len()
            invariant
                index as int <= arr@.len(),
                odd_numbers@ == filter_odd(arr@.subrange(0, index as int)),
                arr.len() == input_len,
        {
            if (arr[index] % 2 != 0) {
                odd_numbers.push(arr[index]);
                proof {
                    assert(odd_numbers@ == filter_odd(arr@.subrange(0, (index + 1) as int)));
                }
            }
            index += 1;
        }

        // Proof block to ensure final condition after the loop
        proof {
            assert(odd_numbers@ == filter_odd(arr@));
        }

        odd_numbers
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpvvhplrma`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False