
use vstd::prelude::*;

fn main() {}

verus! {

fn find_negative_numbers(arr: &Vec<i32>) -> (negative_list: Vec<i32>)
    ensures
        negative_list@ == arr@.filter(|x: i32| x < 0),
{
    proof {
        reveal(Seq::filter);
    }

    let mut negative_list: Vec<i32> = Vec::new();
    let mut index = 0;

    assert(negative_list@ == arr@.subrange(0, index as int).filter(|x: i32| x < 0));

    while index < arr.len()
        invariant
            index <= arr.len(),
            negative_list@ == arr@.subrange(0, index as int).filter(|x: i32| x < 0),
            arr.len() == arr.len(), // We maintain the length invariant
    {
        if arr[index] < 0 {
            negative_list.push(arr[index]);
            // Proof after pushing a negative element
            proof {
                assert(negative_list@ == arr@.subrange(0, index as int + 1).filter(|x: i32| x < 0));
            }
        }
        index += 1;
    }

    proof {
        lemma_seq_subrange_all(arr@);
        assert(negative_list@ == arr@.filter(|x: i32| x < 0)); // Final check to ensure the output matches the postcondition
    }

    negative_list
}

proof fn lemma_seq_subrange_ascend<T>(v: Seq<T>, i: int, j: int)
    requires
        0 <= i < j <= v.len(),
    ensures
        v.subrange(i as int, j as int).drop_last() == v.subrange(i as int, j - 1),
{
    assert(v.subrange(i as int, j as int).drop_last() =~= v.subrange(i as int, j - 1));
}

proof fn lemma_seq_subrange_all<T>(v: Seq<T>)
    ensures
        v == v.subrange(0, v.len() as int),
{
    assert(v =~= v.subrange(0, v.len() as int));
}

} // verus!

### Changes made:
1. Added this proof block inside the `if` statement to ensure the invariant and postcondition are correctly captured:
   rust
   proof {
       assert(negative_list@ == arr@.subrange(0, index as int + 1).filter(|x: i32| x < 0));
   }
   
2. Added a final proof block just before returning the result to reassert that the `negative_list` matches the filtered array:
   rust
   proof {
       lemma_seq_subrange_all(arr@);
       assert(negative_list@ == arr@.filter(|x: i32| x < 0)); // Final check to ensure the output matches the postcondition
   }
   

// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmphnvyaqjm`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 5
// Safe: False