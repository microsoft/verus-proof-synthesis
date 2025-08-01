use vstd::prelude::*;
fn main() {}

verus! {

fn remove_kth_element(list: &Vec<i32>, k: usize) -> (new_list: Vec<i32>)
    requires
        list.len() > 0,
        0 < k < list@.len(),
    ensures
        new_list@ == list@.subrange(0, k - 1 as int).add(
            list@.subrange(k as int, list.len() as int),
        ),
{
    let mut new_list = Vec::new();
    let mut index = 0;
    proof {
        assert(new_list@.len() == 0);
    }
    while index < (k - 1)
    invariant
        0 <= index <= k - 1,
        new_list@ == list@.subrange(0, index as int),
    {
        new_list.push(list[index]);
        index += 1;
        proof {
            assert(new_list@ == list@.subrange(0, index as int));
        }
    }

    let mut index2 = k;
    proof {
        assert(new_list@ == list@.subrange(0, (k - 1) as int));
    }
    while index2 < list.len()
    invariant
        k <= index2 <= list.len(),
        new_list@ == list@.subrange(0, (k - 1) as int).add(
            list@.subrange(k as int, index2 as int)
        ),
    {
        new_list.push(list[index2]);
        index2 += 1;
        proof {
            assert(new_list@ == list@.subrange(0, (k - 1) as int).add(
                list@.subrange(k as int, index2 as int)
            ));
        }
    }

    new_list
}

} // verus!
// Score: (1, 4)
// Safe: False