use vstd::prelude::*;

fn main() {}

verus! {

fn find_negative_numbers(arr: &Vec<i32>) -> (negative_list: Vec<i32>)
    ensures
        negative_list@ == arr@.filter(|x: i32| x < 0),
{
    let mut negative_list: Vec<i32> = Vec::new();
    let mut index = 0;
    
    proof {
        assert(negative_list@ == arr@.take(0).filter(|x: i32| x < 0));
    } // Added by AI 
    
    while index < arr.len() 
        invariant
            index <= arr.len(),
            negative_list@ == arr@.take(index as int).filter(|x: i32| x < 0),
    {
        if arr[index] < 0 {
            negative_list.push(arr[index]);
        }
        
        proof {
            assert(arr@.take(index as int + 1).drop_last() == arr@.take(index as int));
            reveal(Seq::filter);
        } // Added by AI
        
        index += 1;
    }
    
    proof {
        assert(arr@ == arr@.take(arr.len() as int));
    } // Added by AI
    
    negative_list
}

} // verus!
// Score: (2, 0)
// Safe: False