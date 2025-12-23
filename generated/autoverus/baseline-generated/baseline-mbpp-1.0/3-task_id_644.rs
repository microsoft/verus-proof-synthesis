use vstd::prelude::*;
fn main() {}

verus! {

fn reverse_to_k(list: &Vec<i32>, n: usize) -> (reversed_list: Vec<i32>)
    requires
        list@.len() > 0,
        0 < n < list@.len(),
    ensures
        reversed_list@ == list@.subrange(0, n as int).reverse().add(
            list@.subrange(n as int, list.len() as int),
        ),
{
    let mut reversed_list = Vec::new();
    let mut index = 0;
    
    // Proof block: Initialization
    proof {
        assert(reversed_list@ == Seq::<i32>::empty());
    }

    while index < n
        invariant 
            0 <= index <= n,
            reversed_list@ == list@.subrange(0, index as int).reverse()
    {
        reversed_list.push(list[n - 1 - index]);

        // Proof block: After push operation in the first loop
        proof {
            let tmp_list = list@.subrange(0, index as int + 1);
            assert(reversed_list@ == tmp_list.reverse());
        }

        index += 1;
    }

    index = n;

    while index < list.len()
        invariant
            n <= index <= list.len(),
            reversed_list@ == list@.subrange(0, n as int).reverse().add(
                list@.subrange(n as int, index as int)
            )
    {
        reversed_list.push(list[index]);

        // Proof block: After push operation in the second loop
        proof {
            let tmp_rev = list@.subrange(n as int, index as int + 1);
            assert(reversed_list@ == list@.subrange(0, n as int).reverse().add(
                tmp_rev
            ));
        }

        index += 1;
    }
    
    reversed_list
}

} // verus!
// Score: (2, 2)
// Safe: True