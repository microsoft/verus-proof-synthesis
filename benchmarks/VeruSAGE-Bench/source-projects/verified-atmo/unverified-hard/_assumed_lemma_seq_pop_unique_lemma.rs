use vstd::prelude::*;

pub fn main() {}

verus! {


pub proof fn seq_pop_unique_lemma<A>()
    ensures
        forall|s: Seq<A>, i: int|
            s.len() >= 1 && s.no_duplicates() && 0 <= i < s.len() - 1 ==> !s.drop_last().contains(s[s.len() - 1]) && s.drop_last()[i] == s[i],
        forall|s: Seq<A>, v: A|
            s.len() >= 1 && s.no_duplicates() && s[s.len() - 1] == v ==> s.drop_last().to_set().contains(v)
                == false,
        forall|s: Seq<A>, v: A|
            s.len() >= 1 && s.no_duplicates() && s[s.len() - 1] != v ==> s.drop_last().to_set().contains(v)
                == s.to_set().contains(v),
{
}

}
