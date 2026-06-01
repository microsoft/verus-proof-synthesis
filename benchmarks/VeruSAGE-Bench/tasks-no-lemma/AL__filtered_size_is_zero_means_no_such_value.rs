use vstd::{multiset::*, prelude::*};

fn main() {}

verus! {

pub proof fn filtered_size_is_zero_means_no_such_value<V>(m: Multiset<V>, f: spec_fn(V) -> bool)
    ensures (m.filter(f).len() == 0) == (forall |v: V| !(#[trigger] m.contains(v) && f(v)))
{
}

}
