use vstd::prelude::*;

fn main() {}

verus! {

fn find_negative_numbers(arr: &Vec<i32>) -> (negative_list: Vec<i32>)
    ensures
        negative_list@ == arr@.filter(|x: i32| x < 0),
{
    let mut negative_list: Vec<i32> = Vec::new();
    let mut index = 0;

    /* Initialization proof block */
    proof {
        assert(negative_list@ == arr@.take(0).filter(|x: i32| x < 0));
    }
    
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            // Ensuring length conditions
            arr@.len() == arr.len(),
            negative_list@ == arr@.take(index as int).filter(|x: i32| x < 0),
    {
        if arr[index] < 0 {
            negative_list.push(arr[index]);
        }
        index += 1;

        /* Step proof block */
        proof {
            assert(arr@.take(index as int).drop_last() == arr@.take((index - 1) as int));
            reveal(Seq::filter);
        }
    }

    /* Final proof block */
    proof {
        assert(arr@ == arr@.take(arr.len() as int));
    }

    negative_list
}

} // verus!
// Score: (2, 0)
// Safe: False