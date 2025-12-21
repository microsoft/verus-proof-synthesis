use vstd::prelude::*;

fn main() {}

verus! {

pub proof fn seq_remove_lemma_2<A>()
    ensures
        forall|s: Seq<A>, v: A, x: A|
            x != v && s.no_duplicates() ==> s.remove_value(x).contains(v) == s.contains(v),
        forall|s: Seq<A>, v: A|
            #![auto]
            s.no_duplicates() ==> s.remove_value(v).contains(v) == false,
{
}

}
