use vstd::prelude::*;
verus! {

use crate::util::page_ptr_util_u::*;

#[verifier(external_body)]
pub broadcast proof fn map_equal_implies_submap_each_other<K, V>(a: Map<K, V>, b: Map<K, V>)
    requires
        a =~= b,
    ensures
        #[trigger] a.submap_of(b),
        b.submap_of(a),
{
}

    #[verifier::spinoff_prover]
pub broadcast proof fn submap_by_transitivity<K, V>(a: Map<K, V>, b: Map<K, V>, c: Map<K, V>)
    requires
        #[trigger] a.submap_of(b),
        #[trigger] b.submap_of(c),
    ensures
        a.submap_of(c),
{
    assert(forall|k: K|
        #![trigger a.dom().contains(k)]
        #![trigger b.dom().contains(k)]
        a.dom().contains(k) ==> b.dom().contains(k) && a[k] == b[k]);
}

    #[verifier::spinoff_prover]
pub proof fn page_ptr_valid_imply_MEM_valid(v: usize)
    requires
        page_ptr_valid(v),
    ensures
        MEM_valid(v),
{
    assert(v & (!0x0000_ffff_ffff_f000u64) as usize == 0) by (bit_vector)
        requires
            ((v % 4096) == 0) && ((v / 4096) < 2 * 1024 * 1024),
    ;
}

#[verifier(external_body)]
pub proof fn seq_push_lemma<A>()
    ensures
        forall|s: Seq<A>, v: A, x: A|
            s.contains(x) ==> s.push(v).contains(v) && s.push(v).contains(x),
        forall|s: Seq<A>, v: A| #![auto] s.push(v).contains(v),
        forall|s: Seq<A>, v: A, x: A| !s.contains(x) && v != x ==> !s.push(v).contains(x),
{
}
#[verifier(external_body)]
pub proof fn seq_push_index_of_lemma<A>()
    ensures
        forall|s: Seq<A>, v: A, x: A|
            s.no_duplicates() && s.contains(v) && v != x
            ==> 
            s.push(x).index_of(v) == s.index_of(v),
{
}

#[verifier(external_body)]
pub proof fn seq_skip_index_of_lemma<A>()
    ensures
        forall|s: Seq<A>, v: A,|
            #![auto]
            s.len() != 0 && s.no_duplicates() && s.contains(v) && s[0] != v
            ==> 
            s.skip(1).index_of(v) == s.index_of(v) - 1,
{
}

#[verifier(external_body)]
pub proof fn seq_to_set_lemma<A>()
    ensures
        forall|s: Seq<A>, a: A|
            #![trigger s.contains(a)]
            #![trigger s.to_set().contains(a)]
            s.contains(a) == s.to_set().contains(a),
{
}

#[verifier(external_body)]
pub proof fn seq_pop_unique_lemma<A>()
    ensures
        forall|s: Seq<A>, i: int|
            s.no_duplicates() && 0 <= i < s.len() - 1 ==> s.drop_last().contains(s[s.len() - 1])
                && s.drop_last()[i] == s[i],
        forall|s: Seq<A>, v: A|
            s.no_duplicates() && s[s.len() - 1] == v ==> s.drop_last().to_set().contains(v)
                == false,
        forall|s: Seq<A>, v: A|
            s.no_duplicates() && s[s.len() - 1] != v ==> s.drop_last().to_set().contains(v)
                == s.to_set().contains(v),
{
}

#[verifier(external_body)]
pub proof fn seq_update_lemma<A>()
    ensures
        forall|s: Seq<A>, i: int, j: int, v: A|
            0 <= i < s.len() && 0 <= j < s.len() && i != j ==> s.update(j, v)[i] == s[i]
                && s.update(j, v)[j] == v,
        forall|s: Seq<A>, i: int, v: A|
            #![trigger s.update(i,v)[i]]
            0 <= i < s.len() ==> s.update(i, v)[i] == v,
{
}

#[verifier(external_body)]
pub proof fn map_insert_lemma<A, B>()
    ensures
        forall|m: Map<A, B>, x: A, y: A, v: B| x != y ==> m.insert(x, v)[y] == m[y],
{
}

#[verifier(external_body)]
pub proof fn seq_skip_lemma<A>()
    ensures
        forall|s: Seq<A>, v: A|
            s[0] != v && s.no_duplicates() ==> (s.skip(1).contains(v) == s.contains(v)),
        forall|s: Seq<A>| #![trigger s[0]] s.len() > 0 ==> s.contains(s[0]),
        forall|s: Seq<A>| #![trigger s[0]] s.len() > 0 ==> !s.skip(1).contains(s[0]),
        forall|s: Seq<A>, v: A| s[0] == v && s.no_duplicates() ==> s.skip(1) =~= s.remove_value(v),
        forall|s: Seq<A>, i: int| 0 <= i < s.len() - 1 ==> s.skip(1)[i] == s[i + 1],
{
}

#[verifier(external_body)]
pub proof fn seq_remove_lemma<A>()
    ensures
        forall|s: Seq<A>, v: A, i: int|
            #![trigger s.subrange(0,i), s.contains(v)]
            s.contains(v) && s[i] != v && s.no_duplicates() ==> s.subrange(0, i).add(
                s.subrange(i + 1, s.len() as int),
            ).contains(v),
        forall|s: Seq<A>, v: A, i: int|
            #![trigger s.subrange(0,i), s.contains(v)]
            s.contains(v) && s[i] == v && s.no_duplicates() ==> s.subrange(0, i).add(
                s.subrange(i + 1, s.len() as int),
            ).contains(v) == false,
        forall|s: Seq<A>, i: int, j: int|
            #![trigger s.subrange(0,i), s[j]]
            0 <= j < i ==> s.subrange(0, i).add(s.subrange(i + 1, s.len() as int))[j] == s[j],
        forall|s: Seq<A>, i: int, j: int|
            #![trigger s.subrange(0,i), s[j+1]]
            i <= j < s.len() - 1 ==> s.subrange(0, i).add(s.subrange(i + 1, s.len() as int))[j]
                == s[j + 1],
        forall|s: Seq<A>, v: A, i: int|
            #![trigger s.remove_value(v), s.subrange(0,i)]
            s.contains(v) && s[i] == v && s.no_duplicates() ==> s.subrange(0, i).add(
                s.subrange(i + 1, s.len() as int),
            ) == s.remove_value(v),
{
}

#[verifier(external_body)]
pub proof fn seq_remove_index_of_lemma<A>()
    ensures
        forall|s: Seq<A>, v: A, i: int|
            #![trigger s.index_of(v), s[i]]
            s.contains(v) && s[i] != v && s.no_duplicates() && s.subrange(0, i).contains(v) ==> s.subrange(0, i).add(
                s.subrange(i + 1, s.len() as int),
            ).index_of(v) == s.index_of(v),
        forall|s: Seq<A>, v: A, i: int|
        #![trigger s.index_of(v), s[i]]
            s.contains(v) && s[i] != v && s.no_duplicates() && s.index_of(v) < i ==> s.subrange(0, i).add(
                s.subrange(i + 1, s.len() as int),
            ).index_of(v) == s.index_of(v),
        forall|s: Seq<A>, v: A, i: int|
            #![trigger s.index_of(v), s[i]]
            s.contains(v) && s[i] != v && s.no_duplicates() && s.subrange(i + 1, s.len() as int).contains(v) ==> s.subrange(0, i).add(
                s.subrange(i + 1, s.len() as int),
            ).index_of(v) == s.index_of(v) - 1,
        forall|s: Seq<A>, v: A, i: int|
            #![trigger s.index_of(v), s[i]]
            s.contains(v) && s[i] != v && s.no_duplicates() && s.index_of(v) > i ==> s.subrange(0, i).add(
                s.subrange(i + 1, s.len() as int),
            ).index_of(v) == s.index_of(v) - 1,
{}

#[verifier(external_body)]
pub proof fn seq_push_unique_lemma<A>()
    ensures
        forall|s: Seq<A>, v: A|
            #![auto]
            s.no_duplicates() && s.contains(v) == false ==> s.push(v).no_duplicates() && s.push(
                v,
            ).index_of(v) == s.push(v).len() - 1,
        forall|s: Seq<A>, v: A, y: A|
            #![auto]
            s.no_duplicates() && s.contains(v) && s.contains(y) == false ==> s.push(y).index_of(v)
                == s.index_of(v),
{
}

#[verifier(external_body)]
pub proof fn seq_remove_lemma_2<A>()
    ensures
        forall|s: Seq<A>, v: A, x: A|
            x != v && s.no_duplicates() ==> s.remove_value(x).contains(v) == s.contains(v),
        forall|s: Seq<A>, v: A|
            #![auto]
            s.no_duplicates() ==> s.remove_value(v).contains(v) == false,
{
}

#[verifier(external_body)]
pub proof fn seq_index_lemma<A>()
    ensures
        forall|s: Seq<A>, i: int| #![trigger s[i]] s.no_duplicates() ==> s.index_of(s[i]) == i,
{
}

} // verus!
