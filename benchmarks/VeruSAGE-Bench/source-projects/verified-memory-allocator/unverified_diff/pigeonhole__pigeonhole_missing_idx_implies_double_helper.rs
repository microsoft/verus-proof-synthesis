use vstd::prelude::*;


fn main() {}

verus! {

	#[verifier::external_body]
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
		unimplemented!()
	}

	#[verifier::external_body]
proof fn nat_set_size(s:Set<nat>, bound:nat)
    requires
        forall |i: nat| (0 <= i < bound <==> s.contains(i)),
    ensures
        s.finite(),
        s.len() == bound,
	{
		unimplemented!()
	}

pub proof fn pigeonhole_missing_idx_implies_double_helper(
    m: Map<nat, nat>,
    missing: nat,
    len: nat,
    prev_vals: Set<nat>,
    k: nat,
) -> (dup2: nat)
    requires
        len >= 2,
        forall |i: nat| (0 <= i < len <==> m.dom().contains(i)),
        forall |i: nat| (#[trigger] m.dom().contains(i) ==> (
            0 <= m[i] < len && m[i] != missing
        )),
        0 <= missing < len,
        0 <= k < len,
        prev_vals.finite(),
        prev_vals.len() == k,
        //forall |j| 0 <= j < k ==> #[trigger] prev_vals.contains(m[j]),
        forall |elt| #[trigger] prev_vals.contains(elt) ==> exists |j| 0 <= j < k && m[j] == elt,
    ensures 
        m.dom().contains(dup2),
        exists |dup1| #![auto] dup1 != dup2 && m.dom().contains(dup1) && 0 <= dup1 < len && m[dup1] == m[dup2],
{
    proof_from_false() // TODO: replace with appropriate return value
}

}
