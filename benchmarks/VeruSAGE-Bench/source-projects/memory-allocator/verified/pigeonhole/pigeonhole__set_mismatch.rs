use vstd::prelude::*;

fn main(){}

verus! {

	#[verifier::external_body]
proof fn singleton_set_unique_elt<T>(s: Set<T>, a:T, b:T)
    requires
        s.finite(),
        s.len() == 1,
        s.contains(a),
        s.contains(b),
    ensures
        a == b,
	{
		unimplemented!()
	}

proof fn set_mismatch(s1:Set<nat>, s2:Set<nat>, missing:nat)
    requires
        s1.finite(),
        s2.finite(),
        s1.len() == s2.len(),
        forall |elt| s2.contains(elt) ==> s1.contains(elt),
        s1.contains(missing),
        !s2.contains(missing),
    ensures
        false,
    decreases s1.len(),
{
    if s1.len() == 1 {
        let elt = s2.choose();
        assert(s2.contains(elt));
        assert(s1.contains(elt));
        singleton_set_unique_elt(s1, elt, missing);
        assert(elt == missing);
        assert(false);
    } else {
        let elt = s2.choose();
        assert(s2.contains(elt));
        assert(s1.contains(elt));
        let s1_smaller = s1.remove(elt);
        set_mismatch(s1_smaller, s2.remove(elt), missing);
    }
}

}
