use vstd::prelude::*;

fn main() {}

verus! {

proof fn lemma_even_numbers_stability<T>(v: Seq<T>, x: T, index: int)
    requires
        0 <= index <= v.len(),
    ensures
        v.subrange(0, index).filter(|n: T| n % 2 == 0) + x.filter(|n: T| n % 2 == 0) ==
        v.subrange(0, index).filter(|n: T| n % 2 == 0).push(x).filter(|n: T| n % 2 == 0),
{
    // This function would prove that adding an even number to the end of the sequence
    // and then filtering for even numbers is the same as adding that even number
    // directly to the filtered sequence. It's a placeholder for the real proof.
}

fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
{
    let mut even_numbers: Vec<u32> = Vec::new();
    let mut index = 0;

    while index < arr.len() 
        invariant
            index <= arr.len(),
            even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0),
    {
        if (arr[index] % 2 == 0) {
            even_numbers.push(arr[index]);
            proof {
                lemma_even_numbers_stability(arr@, arr[index], index as int);
            }
        }
        index += 1;
    }

    even_numbers
}

} // verus!
// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 6