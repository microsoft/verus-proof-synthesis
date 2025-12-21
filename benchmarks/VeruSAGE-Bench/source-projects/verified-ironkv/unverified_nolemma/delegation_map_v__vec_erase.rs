use vstd::prelude::*;

fn main() {}

verus! {
pub fn vec_erase<A>(v: &mut Vec<A>, start: usize, end: usize)
    requires
        start <= end <= old(v).len(),
    ensures
        true,
        v@ == old(v)@.subrange(0, start as int) + old(v)@.subrange(
            end as int,
            old(v)@.len() as int,
        ),
{
    let mut deleted = 0;
    while deleted < end - start {
        v.remove(start);
        deleted = deleted + 1;
    }
}

} // verus!
