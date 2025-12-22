use vstd::prelude::*;

fn main() {}


verus! {

proof fn lemma_map_distribute<S,T>(s1: Set<S>, s2: Set<S>, f: spec_fn(S) -> T)
    ensures s1.union(s2).map(f) == s1.map(f).union(s2.map(f))
{
    assert forall|x:T| #![auto] s1.map(f).union(s2.map(f)).contains(x) implies s1.union(s2).map(f).contains(x) by {
        if s1.map(f).contains(x) {
            assert(s1.union(s2).contains(choose|y:S| s1.contains(y) && f(y) == x));
        } else {
            assert(s1.union(s2).contains(choose|y:S| s2.contains(y) && f(y) == x));
        }
    }
    assert(s1.union(s2).map(f) =~= s1.map(f).union(s2.map(f)));
}

}
