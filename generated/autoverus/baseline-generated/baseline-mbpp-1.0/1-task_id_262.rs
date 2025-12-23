use vstd::prelude::*;
fn main() {}

verus! {

fn split_array(list: &Vec<i32>, l: usize) -> (new_list: (Vec<i32>, Vec<i32>))
    requires
        list@.len() > 0,
        0 < l < list@.len(),
    ensures
        new_list.0@ == list@.subrange(0, l as int),
        new_list.1@ == list@.subrange(l as int, list.len() as int),
{
    let mut part1: Vec<i32> = Vec::new();
    let mut index = 0;
    proof {
        assert(list@.subrange(0, 0) == Seq::<i32>::empty());
    }
    while index < l
        invariant
            0 <= index <= l,
            part1@ == list@.subrange(0, index as int),
            list@.len() > 0,
            0 < l < list@.len(),
    {
        part1.push(list[index]);
        proof {
            assert(
                part1@ == list@.subrange(0, (index + 1) as int)
            );
        }
        index += 1;
    }
    proof {
        assert(part1@ == list@.subrange(0, l as int));
    }
    
    let mut part2: Vec<i32> = Vec::new();
    index = l;
    proof {
        assert(list@.subrange(l as int, l as int) == Seq::<i32>::empty());
    }
    while index < list.len()
        invariant
            l <= index <= list.len(),
            part2@ == list@.subrange(l as int, index as int),
            list@.len() > 0,
            0 < l < list@.len(),
    {
        part2.push(list[index]);
        proof {
            assert(
                part2@ == list@.subrange(l as int, (index + 1) as int)
            );
        }
        index += 1;
    }
    proof {
        assert(part2@ == list@.subrange(l as int, list.len() as int));
    }
    (part1, part2)
}

} // verus!
// Score: (3, 0)
// Safe: True