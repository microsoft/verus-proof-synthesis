use vstd::prelude::*;

pub fn main() {}

verus! {


pub proof fn seq_push_index_of_lemma<A>()
    ensures
        forall|s: Seq<A>, v: A, x: A|
            s.no_duplicates() && s.contains(v) && v != x
            ==> 
            s.push(x).index_of(v) == s.index_of(v),
{
}

}
