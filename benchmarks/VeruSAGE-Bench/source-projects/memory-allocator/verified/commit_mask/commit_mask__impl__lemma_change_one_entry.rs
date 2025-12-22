use vstd::prelude::*;

fn main(){}

verus! {

	#[verifier::external_body]
proof fn lemma_map_distribute_auto<S,T>()
    ensures forall|s1: Set<S>, s2: Set<S>, f: spec_fn(S) -> T| s1.union(s2).map(f) == #[trigger] s1.map(f).union(s2.map(f))
	{
		unimplemented!()
	}


#[verifier::opaque]
spec fn is_bit_set(a: usize, b: usize) -> bool {
    a & (1usize << b) == (1usize << b)
}

	#[verifier::external_body]
proof fn lemma_is_bit_set()
    ensures
        forall|j: usize| j < 64 ==> !(#[trigger] is_bit_set(0, j)),
        forall|j: usize| is_bit_set(!0usize, j),
        forall|a: usize, b: usize, j: usize| #[trigger] is_bit_set(a | b, j)  <==> is_bit_set(a, j) || is_bit_set(b, j),
        forall|a: usize, b: usize, j: usize| j < 64 ==> (#[trigger] is_bit_set(a & !b, j) <==> is_bit_set(a, j) && !is_bit_set(b, j)),
        forall|a: usize, b: usize, j: usize| #[trigger] is_bit_set(a & b, j)  <==> is_bit_set(a, j) && is_bit_set(b, j),
        // Implied by previous properties, possibly too aggressive trigger
        forall|a: usize, b: usize, j: usize| j < 64 ==> (a & b == 0) ==> !(#[trigger] is_bit_set(a, j) && #[trigger] is_bit_set(b, j)),
	{
		unimplemented!()
	}

pub struct CommitMask {
    mask: [usize; 8],     // size = COMMIT_MASK_FIELD_COUNT
}

impl CommitMask{

    pub closed spec fn view(&self) -> Set<int> {
        Set::new(|t: (int, usize)|
                 0 <= t.0 < 8 && t.1 < 64
                 && is_bit_set(self.mask[t.0], t.1)
        ).map(|t: (int, usize)| t.0 * 64 + t.1)
    }

    proof fn lemma_change_one_entry(&self, other: &Self, i: int)
        requires
            0 <= i < 8,
            self.mask[i] == 0,
            forall|j: int| 0 <= j < i ==> other.mask[j] == self.mask[j],
            forall|j: int| i < j < 8 ==> other.mask[j] == self.mask[j],
        ensures
            other@ == self@.union(Set::new(|b: usize| b < 64 && is_bit_set(other.mask[i], b)).map(|b: usize| 64 * i + b)),
    {
        let s_un = Set::new(|b: usize| b < 64 && is_bit_set(other.mask[i], b));
        let f_un = |b: usize| 64 * i + b;
        let f = |t: (int, usize)| t.0 * 64 + t.1;
        let s_full = Set::new(|t: (int, usize)| 0 <= t.0 < 8 && t.1 < 64 && is_bit_set(self.mask[t.0], t.1));
        let s_full_o = Set::new(|t: (int, usize)| 0 <= t.0 < 8 && t.1 < 64 && is_bit_set(other.mask[t.0], t.1));
        let s1 = Set::new(|t: (int, usize)| 0 <= t.0 < i && t.1 < 64 && is_bit_set(self.mask[t.0], t.1));
        let s2 = Set::new(|t: (int, usize)| t.0 == i && t.1 < 64 && is_bit_set(self.mask[i], t.1));
        let s2o = Set::new(|t: (int, usize)| t.0 == i && t.1 < 64 && is_bit_set(other.mask[i], t.1));
        let s3 = Set::new(|t: (int, usize)| i <  t.0 < 8 && t.1 < 64 && is_bit_set(self.mask[t.0], t.1));
        assert(s_full =~= s1.union(s2).union(s3));
        assert(s2 =~= Set::empty()) by { lemma_is_bit_set(); }
        lemma_map_distribute_auto::<(int,usize),int>();
        assert(s_full.map(f) =~= s1.map(f).union(s2.map(f)).union(s3.map(f)));
        assert(s_full_o =~= s_full.union(s2o));
        assert forall|x| #![auto] s_un.map(f_un).contains(x) implies s2o.map(f).contains(x) by {
            assert(s2o.contains((i, choose|y| s_un.contains(y) && f_un(y) == x)));
        };
        assert forall|x| #![auto] s2o.map(f).contains(x) implies s_un.map(f_un).contains(x) by {
            let y = choose|y| s2o.contains(y) && f(y) == x;
            assert(Set::new(|b: usize| b < 64 && is_bit_set(other.mask[i], b)).contains(y.1));
        };
        assert(s_un.map(f_un) =~= s2o.map(f));
    }
}

}
