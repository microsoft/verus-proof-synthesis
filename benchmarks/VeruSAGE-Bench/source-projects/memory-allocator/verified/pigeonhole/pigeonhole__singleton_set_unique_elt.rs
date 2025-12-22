use vstd::prelude::*;
use vstd::assert_by_contradiction;

fn main(){}

verus! {

proof fn singleton_set_unique_elt<T>(s: Set<T>, a:T, b:T)
    requires
        s.finite(),
        s.len() == 1,
        s.contains(a),
        s.contains(b),
    ensures
        a == b,
{
    assert_by_contradiction!(a == b, {
        let empty = s.remove(a);
        assert(empty.len() == 0);
        assert(empty.contains(b));
    });

}

}
