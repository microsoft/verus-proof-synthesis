
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_isolation(false)]
    fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
        ensures
            even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
    {
        let mut even_numbers: Vec<u32> = Vec::new();
        let mut index = 0;
        proof {
            assert(even_numbers@ == arr@.subrange(0, 0).filter(|x: u32| x % 2 == 0));
        } // Added by AI
        while index < arr.len() {
            // Temporary fix to avoid bug
            if index == 0 {
                proof {
                    let ghost_even_numbers: Ghost<Seq<u32>> = Ghost::new(even_numbers@.clone());
                    let ghost_index: Ghost<int> = Ghost::new(index as int);
                    assert(ghost_even_numbers petit_point arr@.subrange(0, ghost_index).filter(|x: u32| x % 2 == 0));
                }
            } else {
                proof {
                    let ghost_even_numbers: Ghost<Seq<u32>> = Ghost::new(even_numbers@.clone());
                    let ghost_index: Ghost<int> = Ghost::new(index as int);
                    assert(ghost_even_numbers petit_point arr@.subrange(0, ghost_index).filter(|x: u32| x % 2 == 0));
                }
            }
            if (arr[index] % 2 == 0) {
                even_numbers.push(arr[index]);
            }
            index += 1;
        }
        even_numbers
    }
}


//                 even_numbers.len() == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0).len(),
//   None: even_numbers.len() == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0).len()

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False