use vstd::prelude::*;
fn main() {}

verus! {

proof fn lemma_seq_addition_property<T>(v: Seq<T>, n: int)
    requires
        0 <= n <= v.len(),
    ensures
        v.subrange(n, ( v.len() ) as int).add(v.subrange(0, n)) == v,
{
    assert(v =~= v.subrange(n, ( v.len() ) as int).add(v.subrange(0, n)));
}

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
            0 < n < list@.len(),
            new_list@ == list@.subrange(( n ) as int, index as int),
            n <= index <= list.len(),
    {
        new_list.push(list[index]);
        index += 1;
    }

    let mut index = 0;

    while index < n
        invariant
            0 < n < list@.len(),
            new_list@ == list@.subrange(( n ) as int, list.len() as int).add(list@.subrange(0, index as int)),
            0 <= index <= n,
    {
        new_list.push(list[index]);
        index += 1;
    }
    
    proof {
        lemma_seq_addition_property(list@, n as int);
    }

    new_list
}

} // verus!




// is safe: True
// Score: Compilation Error: False, Verified: 0, Errors: 4, Verus Errors: 5