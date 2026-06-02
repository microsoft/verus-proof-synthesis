use vstd::{multiset::*, prelude::*};

fn main() {}

verus! {

pub proof fn filtered_size_is_one_means_only_one_such_value<V>(m: Multiset<V>, f: spec_fn(V) -> bool)
    ensures
        (m.filter(f).len() == 1) == {
            &&& exists |v| #[trigger] m.contains(v) && f(v)
            &&& forall |v| #[trigger] m.contains(v) && f(v) ==> {
                &&& m.count(v) == 1
                &&& forall |u: V| #[trigger] m.contains(u) && f(u) ==> u == v
            }
        }
{
}

}
