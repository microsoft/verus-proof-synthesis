use vstd::prelude::*;

fn main() {}

verus! {

pub proof fn seq_index_lemma<A>()
    ensures
        forall|s: Seq<A>, i: int| #![trigger s[i]] 0 <= i < s.len() && s.no_duplicates() ==> s.index_of(s[i]) == i,
{
}

}
