use vstd::prelude::*;
fn main() {}

verus! {

proof fn lemma_seq_subrange_append<T>(v: Seq<T>, start: int, end: int)
    requires
        0 <= start <= end <= v.len(),
    ensures
        v.subrange(start, end).add(v.subrange(0, start)) =~= v,
{
    assert(v.subrange(start, end).add(v.subrange(0, start)) =~= v.subrange(0, end).add(v.subrange(0, start)));
    assert(v.subrange(start, end).add(v.subrange(0, start)) =~= v.subrange(0, end).add(v.subrange(end, end)).add(v.subrange(0, start)));
    assert(v.subrange(start, end).add(v.subrange(0, start)) =~= v.subrange(0, end).add(v.subrange(0, 0)).add(v.subrange(0, start)));
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
            index <= list.len(),
            new_list.len() == index - n,
            forall |i: int| 0 <= i < new_list.len() ==> new_list[i] == list[n + i],
            list.len() > 0,
            0 < n < list.len(),
    {
        new_list.push(list[index]);
        index += 1;
    }

    index = 0;

    while index < n
        invariant
            index <= n,
            new_list.len() == list.len() - n + index,
            forall |i: int| 0 <= i < list.len() - n ==> new_list[i] == list[n + i],
            forall |i: int| 0 <= i < index ==> new_list[list.len() - n + i] == list[i],
            list.len() > 0,
            0 < n < list.len(),
    {
        new_list.push(list[index]);
        index += 1;
    }

    new_list
}

} // verus!
// is safe: False
// Score: Compilation Error: False, Verified: 2, Errors: 2, Verus Errors: 3