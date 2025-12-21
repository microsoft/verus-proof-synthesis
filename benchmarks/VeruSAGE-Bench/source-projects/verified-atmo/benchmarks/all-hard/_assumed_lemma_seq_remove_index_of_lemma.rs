use vstd::prelude::*;

fn main() {}

verus! {

pub proof fn seq_remove_index_of_lemma<A>()
    ensures
        forall|s: Seq<A>, v: A, i: int|
            #![trigger s.index_of(v), s[i]]
            0 <= i < s.len() && s.contains(v) && s[i] != v && s.no_duplicates() && s.subrange(0, i).contains(v) ==> s.subrange(0, i).add(
                s.subrange(i + 1, s.len() as int),
            ).index_of(v) == s.index_of(v),
        forall|s: Seq<A>, v: A, i: int|
        #![trigger s.index_of(v), s[i]]
            0 <= i < s.len() && s.contains(v) && s[i] != v && s.no_duplicates() && s.index_of(v) < i ==> s.subrange(0, i).add(
                s.subrange(i + 1, s.len() as int),
            ).index_of(v) == s.index_of(v),
        forall|s: Seq<A>, v: A, i: int|
            #![trigger s.index_of(v), s[i]]
            0 <= i < s.len() && s.contains(v) && s[i] != v && s.no_duplicates() && s.subrange(i + 1, s.len() as int).contains(v) ==> s.subrange(0, i).add(
                s.subrange(i + 1, s.len() as int),
            ).index_of(v) == s.index_of(v) - 1,
        forall|s: Seq<A>, v: A, i: int|
            #![trigger s.index_of(v), s[i]]
            0 <= i < s.len() && s.contains(v) && s[i] != v && s.no_duplicates() && s.index_of(v) > i ==> s.subrange(0, i).add(
                s.subrange(i + 1, s.len() as int),
            ).index_of(v) == s.index_of(v) - 1,
{}

}
