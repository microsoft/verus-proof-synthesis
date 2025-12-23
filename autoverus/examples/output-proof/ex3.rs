#[allow(unused_imports)]
use vstd::prelude::*;
fn main() {}

verus! {
spec fn seq_to_set_rec<A>(seq: Seq<A>) -> Set<A>
    decreases seq.len()
{
    if seq.len() == 0 {
        Set::empty()
    } else {
        seq_to_set_rec(seq.drop_last()).insert(seq.last())
    }
}

/// helper function showing that the resulting set contains all elements of the sequence
proof fn seq_to_set_rec_contains<A>(seq: Seq<A>)
    ensures forall |a| #[trigger] seq.contains(a) <==> seq_to_set_rec(seq).contains(a)
    decreases seq.len()
{
    if seq.len() > 0 {
        assert(forall |a| #[trigger] seq.drop_last().contains(a) <==> seq_to_set_rec(seq.drop_last()).contains(a)) by {
            seq_to_set_rec_contains(seq.drop_last());
        }

        assert(seq.ext_equal(seq.drop_last().push(seq.last())));
        assert forall |a| #[trigger] seq.contains(a) <==> seq_to_set_rec(seq).contains(a) by {
            if !seq.drop_last().contains(a) {
                if a == seq.last() {
                    assert(seq.contains(a));
                    assert(seq_to_set_rec(seq).contains(a));
                } else {
                    assert(!seq_to_set_rec(seq).contains(a));
                }
            }
        }
    }
}

/// helper function showing that the recursive definition matches the set comprehension one
proof fn seq_to_set_equal_rec<A>(seq: Seq<A>)
    ensures seq.to_set() == seq_to_set_rec(seq)
{
    assert(forall |n| #[trigger] seq.contains(n) <==> seq_to_set_rec(seq).contains(n)) by {
        seq_to_set_rec_contains(seq);
    }
    assert(forall |n| #[trigger] seq.contains(n) <==> seq.to_set().contains(n));
    assert(seq.to_set().ext_equal(seq_to_set_rec(seq)));
}

proof fn lemma_seq_push_to_set_insert<T>(s: Seq<T>, val: T)
ensures
    s.push(val).to_set() === s.to_set().insert(val),
{
    seq_to_set_equal_rec(s.push(val));
    assert(s.ext_equal(s.push(val).drop_last()));
    seq_to_set_equal_rec(s);
    assert(s.push(val).to_set() === seq_to_set_rec(s.push(val)));
    assert(s.push(val).to_set() === seq_to_set_rec(s.push(val).drop_last()).insert(val));
}

fn remove_duplicates(nums: Vec<i32>) -> (res: Vec<i32>)
ensures
    res@.no_duplicates(),
    nums@.to_set().ext_equal(res@.to_set())
{
    let mut res = Vec::new();
    let mut i = 0;
    while i < nums.len()
    invariant
        0 <= i <= nums@.len(),
        nums@.subrange(0, i  as int).to_set().ext_equal(res@.to_set()),
        res@.no_duplicates(),
    {
        let mut found = false;
        let mut j = 0;

        while j < res.len()
        invariant
            0 <= i < nums@.len(),
            0 <= j <= res@.len(),
            res@.no_duplicates(),
            nums@.subrange(0, i  as int).to_set().ext_equal(res@.to_set()),
            !found,
            forall |k| 0 <= k < j ==> res@[k] != nums@[i as int],
        ensures
            0<= i < nums@.len(),
            0 <= j <= res@.len(),
            res@.no_duplicates(),
            nums@.subrange(0, i  as int).to_set().ext_equal(res@.to_set()),
            found ==> (j < res@.len() && res@[j as int] == nums@[i as int]),
            !found ==> forall |k| 0 <= k < j ==> res@[k] != nums@[i as int],
            !found ==> j == res@.len(),
        {
            if nums[i] == res[j] {
                found = true;
                break;
            }
            j += 1;
        }
        proof {
            let val = nums@[i as int];
            assert(nums@.subrange(0, i as int + 1).ext_equal(nums@.subrange(0, i as int).push(val)));
            lemma_seq_push_to_set_insert(nums@.subrange(0, i as int), val);
            lemma_seq_push_to_set_insert(res@, val);
            assert(nums@.subrange(0, i as int + 1).to_set().ext_equal(res@.to_set().insert(val)));
            if found {
                assert(res@.contains(val));
                assert(res@.to_set().contains(val));
                assert(res@.to_set().ext_equal(res@.to_set().insert(val)));
                assert(nums@.subrange(0, i as int + 1).to_set().ext_equal(res@.to_set()));
            }
        } // Added by AI
        if !found {
            res.push(nums[i]);
        }
        i += 1;
    }
    proof {
        assert(nums@.subrange(0, i  as int).ext_equal(nums@));
    }
    res
}
}
