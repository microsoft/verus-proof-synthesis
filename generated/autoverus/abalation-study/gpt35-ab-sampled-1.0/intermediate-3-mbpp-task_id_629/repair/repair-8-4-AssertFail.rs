
use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]

proof fn lemma_filter_even_numbers(arr: Vec<u32>, pred: &Trigger<u32>)
    ensures even_numbers@ == arr@.filter(pred),
{
    asserts {
        assert(forall |x: u32| #[trigger] arr.contains(x) <==> arr.filter(pred).contains(x));
        assert(forall |x: u32| #[trigger] arr.filter(pred).contains(x) <==> arr.contains(x) && pred(x));

        let mut even_numbers = Vec::new();
        let mut index = 0;
        while index < arr.len()
            invariant
                index <= arr.len(),
        {
            if pred(arr[index]) {
                even_numbers.push(arr[index]);
            }
            index += 1;
        }
        arr.filter(pred) == even_numbers;
    }
}

fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
    requires
        lemma_filter_even_numbers(arr.clone(), &(|x: u32| x % 2 == 0)),
    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
{
    let mut even_numbers: Vec<u32> = Vec::new();
    let mut index = 0;
    lemma_filter_even_numbers(arr.clone(), &(|x: u32| x % 2 == 0));
    while index < arr.len()
        invariant
            index <= arr.len(),
            lemma_filter_even_numbers(arr.clone(), &(|x: u32| x % 2 == 0)),
    {
        if (arr[index] % 2 == 0) {
            even_numbers.push(arr[index]);
        }
        index += 1;
        lemma_filter_even_numbers(arr.clone(), &(|x: u32| x % 2 == 0));
    }
    lemma_filter_even_numbers(arr.clone(), &(|x: u32| x % 2 == 0));
    even_numbers
}

} // verus!


//     assert(even_numbers@ == arr@.filter(|x: u32| x % 2 == 0)); // Added by AI
//   assertion failed: even_numbers@ == arr@.filter(|x: u32| x % 2 == 0)

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False