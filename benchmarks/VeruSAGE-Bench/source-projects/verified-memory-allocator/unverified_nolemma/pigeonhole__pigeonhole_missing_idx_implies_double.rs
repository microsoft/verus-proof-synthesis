use vstd::prelude::*;


fn main() {}

verus! {

pub proof fn pigeonhole_missing_idx_implies_double(
    m: Map<nat, nat>,
    missing: nat,
    len: nat,
) -> (r: (nat, nat))
    requires
        forall |i: nat| (0 <= i < len <==> m.dom().contains(i)),
        forall |i: nat| (#[trigger] m.dom().contains(i) ==> (
            0 <= m[i] < len && m[i] != missing
        )),
        0 <= missing < len,
    ensures ({ let (i, j) = r;
        i != j
          && m.dom().contains(i)
          && m.dom().contains(j)
          && m[i] == m[j]
    })
{
    proof_from_false() // TODO: replace with appropriate return value
}

}
