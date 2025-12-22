use vstd::prelude::*;

fn main() {}

verus!{

#[verifier::external_body]
pub proof fn push_to_set_eq_to_set_insert<A>(s: Seq<A>, e: A)
    ensures s.push(e).to_set() == s.to_set().insert(e)
{ unimplemented!() }

pub proof fn map_values_to_set_eq_to_set_mk_map_values<A, B>(s: Seq<A>, map: spec_fn(A) -> B)
    ensures s.map_values(map).to_set() == s.to_set().mk_map(map).values(),
    decreases s.len()
{
    if s.len() != 0 {
        let subseq = s.drop_last();
        map_values_to_set_eq_to_set_mk_map_values(subseq, map);
        assert(s.map_values(map).to_set() == subseq.map_values(map).to_set().insert(map(s.last()))) by {
            push_to_set_eq_to_set_insert(subseq.map_values(map), map(s.last()));
            assert(s.map_values(map) == subseq.map_values(map).push(map(s.last())));
        }
        let submap = subseq.to_set().mk_map(map);
        assert(s.map_values(map).to_set() == submap.values().insert(map(s.last())));
        assert(s.to_set().mk_map(map).values() == submap.values().insert(map(s.last()))) by {
            push_to_set_eq_to_set_insert(subseq, s.last());
            assert(s == subseq.push(s.last()));
            assert(s.to_set() == subseq.to_set().insert(s.last()));
            assert(subseq.to_set().insert(s.last()).mk_map(map) == submap.insert(s.last(), map(s.last())));
            assert(s.to_set().mk_map(map) == submap.insert(s.last(), map(s.last())));
            if subseq.to_set().contains(s.last()) {
                assert(submap.contains_pair(s.last(), map(s.last())));
                assert(submap.values().contains(map(s.last())));
                assert(submap.values().insert(map(s.last())) == submap.values());
                assert(s.to_set() == subseq.to_set());
                assert(s.to_set().mk_map(map).values() == submap.values());
            } else {
                assert(submap.values().insert(map(s.last())) =~= submap.insert(s.last(), map(s.last())).values()) by {
                    assert forall |v: B| #[trigger] submap.values().insert(map(s.last())).contains(v)
                           implies submap.insert(s.last(), map(s.last())).contains_value(v) by {
                        if v != map(s.last()) {
                            assert(submap.contains_value(v));
                            assert(exists |k: A| #[trigger] submap.contains_key(k) && submap[k] == v);
                            let k = choose |k: A| #[trigger] submap.contains_key(k) && submap[k] == v;
                            assert(k != s.last()) by {
                                assert(!subseq.to_set().contains(s.last()));
                                assert(!submap.contains_key(s.last()));
                                assert(submap.contains_key(k));
                            }
                            assert(submap.insert(s.last(), map(s.last())).contains_pair(k, v));
                            assert(submap.insert(s.last(), map(s.last())).contains_value(v));
                        } else {
                            assert(submap.insert(s.last(), map(s.last())).contains_pair(s.last(), map(s.last())));
                        }
                    }
                    assert(submap.insert(s.last(), map(s.last())).contains_pair(s.last(), map(s.last())));
                    assert(submap.insert(s.last(), map(s.last())).values().contains(map(s.last())));
                    assert forall |v: B| #[trigger] submap.insert(s.last(), map(s.last())).values().contains(v)
                           implies submap.values().insert(map(s.last())).contains(v) by {
                        if v != map(s.last()) {
                            assert(submap.contains_value(v));
                        }
                    } 
                }
            }
        }
    }
    assert(s.map_values(map).to_set() == s.to_set().mk_map(map).values()); // why it's required
}

}
