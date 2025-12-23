use vstd::prelude::*;
fn main() {}

verus! {

fn split_and_append(list: &Vec<i32>, n: usize) -> (new_list: Vec<i32>)
    requires
        list@.len() > 0,
        0 < n < list@.len(),
    ensures
        new_list@ == list@.subrange(n as int, list@.len() as int).add(list@.subrange(0, n as int)),
{
    let mut new_list = Vec::new();
    let mut index = n;

    while index < list.len() 
        invariant
            list@.len() > 0,
            0 < n < list@.len(),
            new_list@ == list@.subrange(n as int, index as int),
            n <= index <= list.len(),
    {
        proof {
            // Ensuring new_list@ is being constructed correctly by subrange
            assert(new_list@ == list@.subrange(n as int, index as int));
        }
        
        new_list.push(list[index]);
        index += 1;
    }
    
    let mut index = 0;

    while index < n
        invariant
            list@.len() > 0,
            0 < n < list@.len(),
            new_list@ == list@.subrange(n as int, list.len() as int).add(list@.subrange(0, index as int)),
            0 <= index <= n,
    {
        proof {
            // Ensuring new_list@ is being appended correctly by subrange and add operations
            assert(new_list@ == list@.subrange(n as int, list.len() as int).add(list@.subrange(0, index as int)));
        }
        
        new_list.push(list[index]);
        index += 1;
    }

    proof {
        // Final check to ensure the merged result is correct
        assert(new_list@ == list@.subrange(n as int, list@.len() as int).add(list@.subrange(0, n as int)));
    }
    
    new_list
}

} // verus!
// Score: (0, 4)
// Safe: True