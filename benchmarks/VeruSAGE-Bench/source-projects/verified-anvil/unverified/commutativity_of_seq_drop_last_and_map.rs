use vstd::prelude::*;

fn main() {}

verus!{

pub proof fn commutativity_of_seq_drop_last_and_map<A, B>(s: Seq<A>, pred: spec_fn(A) -> B)
    requires s.len() > 0,
    ensures s.drop_last().map_values(pred) == s.map_values(pred).drop_last(),
{
}

}
