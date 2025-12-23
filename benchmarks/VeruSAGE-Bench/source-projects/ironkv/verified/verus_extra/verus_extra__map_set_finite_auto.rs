use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::set_lib::*;

fn main() {}

verus!{

// File: set_lib_ext_v.rs
	#[verifier::external_body]
#[verifier::spinoff_prover]
pub proof fn map_finite<A, B>(s: Set<A>, f: spec_fn(A) -> B)
requires
    s.finite(),
ensures
    s.map(f).finite(),
	{
		unimplemented!()
	}

#[verifier::spinoff_prover]
pub proof fn map_set_finite_auto<A, B>()
ensures
    forall |s: Set<A>, f: spec_fn(A) -> B| s.finite() ==> #[trigger] (s.map(f).finite()),
{
    assert forall |s: Set<A>, f: spec_fn(A) -> B| s.finite() implies #[trigger] s.map(f).finite() by {
        map_finite(s, f);
    }
}


}
