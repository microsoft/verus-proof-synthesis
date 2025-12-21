use vstd::prelude::*;

fn main() {}

verus!{

// File: spec/utils.rs
spec fn seq_to_set_rec<A>(seq: Seq<A>) -> Set<A>
    decreases seq.len(),
    when seq.len() >= 0
    via seq_to_set_rec_decreases::<A>
{
    if seq.len() == 0 {
        Set::empty()
    } else {
        seq_to_set_rec(seq.drop_last()).insert(seq.last())
    }
}

#[via_fn]
proof fn seq_to_set_rec_decreases<A>(seq: Seq<A>) {
    if seq.len() == 0 {
    } else {
        assert(seq.drop_last().len() < seq.len());  // INCOMPLETENESS weird incompleteness again
    }
}

	#[verifier::external_body]
proof fn seq_to_set_rec_contains<A>(seq: Seq<A>)
    ensures
        forall|a| #[trigger] seq.contains(a) <==> seq_to_set_rec(seq).contains(a),
    decreases seq.len(),
	{
		unimplemented!()
	}

proof fn seq_to_set_equal_rec<A>(seq: Seq<A>)
    ensures
        seq_to_set(seq) == seq_to_set_rec(seq),
{
    assert(forall|n| #[trigger] seq.contains(n) <==> seq_to_set_rec(seq).contains(n)) by {
        seq_to_set_rec_contains(seq);
    }
    assert(forall|n| #[trigger] seq.contains(n) <==> seq_to_set(seq).contains(n));
    assert(seq_to_set(seq) =~= seq_to_set_rec(seq));
}

pub open spec fn seq_to_set<A>(seq: Seq<A>) -> Set<A> {
    Set::new(|a: A| seq.contains(a))
}


}
