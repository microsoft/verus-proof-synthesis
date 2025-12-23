use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::set_lib::*;

fn main() {}

verus!{

// File: set_lib_ext_v.rs
#[verifier::spinoff_prover]
pub proof fn lemma_to_set_singleton_auto<A>()
ensures
    forall |x: A| #[trigger] seq![x].to_set() == set![x],
{
    assert forall |x: A| #[trigger] seq![x].to_set() =~= set![x] by {
        assert(seq![x][0] == x);
    }
}


}
