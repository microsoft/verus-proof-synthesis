
use vstd::prelude::*;
fn main() {}

verus! {

proof fn lemma_seq_subrange_all<T>(v: Seq<T>)
    ensures
        v == v.subrange(0, v.len() as int),
{
    assert(v =~= v.subrange(0, v.len() as int));
}

proof fn lemma_seq_subrange_ascend<T>(v: Seq<T>, i:int, j: int)
    requires
        0<= i < j <= v.len(),
    ensures
        v.subrange(i, j as int).drop_last() == v.subrange(i, j-1 ),
{
    assert(v.subrange(i, j as int).drop_last() =~= v.subrange(i, j-1));
}

#[verifier::loop_isolation(false)]

spec fn count_boolean(seq: Seq<bool>) -> int
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_boolean(seq.drop_last()) + if (seq.last()) {
            1 as int
        } else {
            0 as int
        }
    }
}

fn count_true(arr: &Vec<bool>) -> (count: u64)
    ensures
        0 <= count <= arr.len(),
        count_boolean(arr@) == count,
{
    let mut index = 0;
    let mut counter = 0;
    while index < arr.len()
        invariant
            0 <= counter <= index,
            0 <= counter,
            0 <= index <= arr.len(),
            count_boolean(arr@.subrange(0, index as int)) == counter as int,
            index <= arr.len(),
            arr.len() == arr.len(), 
            forall |k: int| 0 <= k < arr.len() ==> arr@[k] == arr@[k],
    {
        if (arr[index]) {
            counter += 1;
        }
        index += 1;
        
        proof {
            if index > 1 {
                lemma_seq_subrange_ascend(arr@, 0, index as int);
            }
            assert(count_boolean(arr@.subrange(0, index as int)) == counter as int);
        }
    }
    proof {
        lemma_seq_subrange_all(arr@);
    }
    counter
}

} // verus!


//             assert(count_boolean(arr@.subrange(0, index as int)) == counter as int);
//   assertion failed: count_boolean(arr@.subrange(0, index as int)) == counter as int

// Compilation Error: False, Verified: 4, Errors: 1, Verus Errors: 1
// Safe: True