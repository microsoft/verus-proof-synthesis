use vstd::prelude::*;
use vstd::set_lib::*;
use vstd::assert_by_contradiction;

fn main() {}


verus! {

pub struct AbstractEndPoint {
    pub id: Seq<u8>,
}

impl Ordering {
    pub open spec fn eq(self) -> bool {
        matches!(self, Ordering::Equal)
    }

    pub open spec fn ne(self) -> bool {
        !matches!(self, Ordering::Equal)
    }

    pub open spec fn lt(self) -> bool {
        matches!(self, Ordering::Less)
    }

    pub open spec fn gt(self) -> bool {
        matches!(self, Ordering::Greater)
    }

    pub open spec fn le(self) -> bool {
        !matches!(self, Ordering::Greater)
    }
}

struct StrictlyOrderedVec<K: KeyTrait> {
    v: Vec<K>,
}

spec fn sorted<K: KeyTrait>(s: Seq<K>) -> bool
{
    forall |i, j| #![auto] 0 <= i < j < s.len() ==> s[i].cmp_spec(s[j]).lt()
}

impl<K: KeyTrait + VerusClone> StrictlyOrderedVec<K> {

    pub closed spec fn view(self) -> Seq<K> {
        self.v@
    }

    pub closed spec fn valid(self) -> bool {
        sorted(self@) && self@.no_duplicates()
    }

	#[verifier::external_body]
    proof fn to_set(self) -> (s: Set<K>)
        requires self.valid(),
        ensures s == self@.to_set(),
                s.finite(),
                s.len() == self@.len(),
	{
		unimplemented!()
	}

	#[verifier::external_body]
    fn len(&self) -> (len: usize )
        ensures len == self@.len()
	{
		unimplemented!()
	}

	#[verifier::external_body]
    fn index(&self, i: usize) -> (k: K)
        requires i < self@.len(),
        ensures k == self@[i as int]
	{
		unimplemented!()
	}

	#[verifier::external_body]
    fn erase(&mut self, start: usize, end: usize)
        requires
            old(self).valid(),
            start <= end <= old(self)@.len(),
        ensures
            self.valid(),
            self@ == old(self)@.subrange(0, start as int) + old(self)@.subrange(end as int, old(self)@.len() as int),
            // TODO: We might want to strengthen this further to say that the two sets on the RHS
            //       are disjoint
            old(self)@.to_set() == self@.to_set() + old(self)@.subrange(start as int, end as int).to_set(),
	{
		unimplemented!()
	}



}

impl<K: KeyTrait + VerusClone> KeyIterator<K> {

    pub open spec fn is_end_spec(&self) -> bool {
        self.k.is_None()
    }

    pub open spec fn get_spec(&self) -> &K
        recommends self.k.is_some(),
    {
        &self.k.get_Some_0()
    }

    spec fn above_spec(&self, k: K) -> bool {
        self.k.is_None() || k.cmp_spec(self.k.get_Some_0()).lt()
    }

	#[verifier::external_body]
    #[verifier(when_used_as_spec(above_spec))]

    fn above(&self, k: K) -> (b: bool)
        ensures b == self.above_spec(k),
	{
		unimplemented!()
	}

    pub open spec fn between(lhs: Self, ki: Self, rhs: Self) -> bool {
        !ki.lt_spec(lhs) && ki.lt_spec(rhs)
    }


    pub open spec fn end_spec() -> (s: Self) {
        KeyIterator { k: None }
    }
#[verifier::spinoff_prover]

    #[verifier(when_used_as_spec(end_spec))]
    pub fn end() -> (s: Self)
        ensures s.k.is_None()
    {
        KeyIterator { k: None }
    }

#[verifier::spinoff_prover]

    #[verifier(when_used_as_spec(is_end_spec))]
    pub fn is_end(&self) -> (b: bool)
        ensures b == self.is_end_spec()
    {
        matches!(self.k, None)
    }

    
#[verifier::spinoff_prover]

    #[verifier(when_used_as_spec(get_spec))]
    pub fn get(&self) -> (k: &K)
        requires !self.is_end(),
        ensures k == self.get_spec(),
    {
        self.k.as_ref().unwrap()
    }

}

	#[verifier::external_body]
pub fn vec_erase<A>(v: &mut Vec<A>, start: usize, end: usize)
    requires
        start <= end <= old(v).len(),
    ensures
        true,
        v@ == old(v)@.subrange(0, start as int) + old(v)@.subrange(end as int, old(v)@.len() as int),
	{
		unimplemented!()
	}

#[verifier::reject_recursive_types(K)]
struct StrictlyOrderedMap<K: KeyTrait + VerusClone> {
    keys: StrictlyOrderedVec<K>,
    vals: Vec<ID>,
    m: Ghost<Map<K, ID>>,
}

impl<K: KeyTrait + VerusClone> StrictlyOrderedMap<K> {

    pub closed spec fn view(self) -> Map<K,ID> {
        self.m@
    }

    pub closed spec fn map_valid(self) -> bool
        // recommends self.keys@.len() == self.vals.len()  // error: public function requires cannot refer to private items
    {
        &&& self.m@.dom().finite()
        &&& self.m@.dom() == self.keys@.to_set()
        &&& forall |i| 0 <= i < self.keys@.len() ==> #[trigger] (self.m@[self.keys@.index(i)]) == self.vals@.index(i)
    }

    pub closed spec fn valid(self) -> bool {
        &&& self.keys.valid()
        &&& self.keys@.len() == self.vals.len()
        &&& self.map_valid()
    }

    spec fn gap(self, lo: KeyIterator<K>, hi: KeyIterator<K>) -> bool {
        forall |ki| lo.lt_spec(ki) && ki.lt_spec(hi) ==> !(#[trigger] self@.contains_key(*ki.get()))
    }

	#[verifier::external_body]
    proof fn gap_means_empty(self, lo:KeyIterator<K>, hi:KeyIterator<K>, k:KeyIterator<K>)
        requires
            self.gap(lo, hi),
            lo.lt_spec(k) && k.lt_spec(hi),
            self@.contains_key(*k.get()),
        ensures
            false,
	{
		unimplemented!()
	}

	#[verifier::external_body]
    proof fn choose_gap_violator(self, lo:KeyIterator<K>, hi:KeyIterator<K>) -> (r: KeyIterator<K>)
        requires
            !self.gap(lo, hi),
        ensures
            lo.lt_spec(r) && r.lt_spec(hi) && self@.contains_key(*r.get()),
	{
		unimplemented!()
	}

    fn erase(&mut self, lo: &KeyIterator<K>, hi: &KeyIterator<K>)
        requires
            old(self).valid(),
        ensures
            self.valid(),
            forall |k| {
                let ki = KeyIterator::new_spec(k);
                (if ki.geq_spec(*lo) && ki.lt_spec(*hi) {
                    !(#[trigger] self@.contains_key(k))
                } else {
                    (old(self)@.contains_key(k) ==>
                         self@.contains_key(k) && self@[k] == old(self)@[k])
                    && (self@.contains_key(k) ==> old(self)@.contains_key(k))
                })},
            forall |x, y| self.gap(x, y) <==> ({
                         ||| old(self).gap(x, y)
                         ||| (old(self).gap(x, *lo) &&
                              old(self).gap(*hi, y) &&
                              (hi.geq_spec(y) || hi.is_end_spec() || !self@.contains_key(*hi.get())))
                        }),
    {
        // Find the point where keys are >= lo
        let mut start = 0;
        while start < self.keys.len() && lo.above(self.keys.index(start))
            invariant
                self.valid(),
                0 <= start <= self.keys@.len(),
                forall |j| #![auto] 0 <= j < start ==> lo.above(self.keys@.index(j))
            decreases
                self.keys@.len() - start
        {
            start = start + 1;
        }

        // Find the first point where keys are >= hi
        let mut end = start;
        while end < self.keys.len() && hi.above(self.keys.index(end))
            invariant
                self.valid(),
                start <= end <= self.keys@.len(),
                forall |j| #![auto] start <= j < end ==> hi.above(self.keys@[j])
            decreases
                self.keys@.len() - end
        {
            end = end + 1;
        }

        //assert(forall |i| #![auto] 0 <= i < start ==> lo.above(self.keys@.index(i)));
        assert forall |i| start <= i < end implies !lo.above(#[trigger] self.keys@[i]) && hi.above(self.keys@[i]) by {
            K::cmp_properties();
        }

        self.keys.erase(start, end);
        vec_erase(&mut self.vals, start, end);
        self.m = Ghost(Map::new(|k| self.keys@.to_set().contains(k),
                                |k| { let i = choose |i| 0 <= i < self.keys@.len() && self.keys@[i] == k;
                                      self.vals@[i]}));
        proof {
            let ks = self.keys.to_set();
            assert(self.keys@.to_set() == ks);
            assert_sets_equal!(self.m@.dom(), ks);
        }

        assert forall |k| {
                let ki = KeyIterator::new_spec(k);
                (if ki.geq_spec(*lo) && ki.lt_spec(*hi) {
                    !(#[trigger] self@.contains_key(k))
                } else {
                    old(self)@.contains_key(k) ==>
                        self@.contains_key(k) && self@[k] == old(self)@[k]
                })} by {

            let ki = KeyIterator::new_spec(k);
            if ki.geq_spec(*lo) && ki.lt_spec(*hi) {
                assert_by_contradiction!(!self@.contains_key(k), {
                    K::cmp_properties();
                });
            }
        }
        assert forall |x, y| self.gap(x, y) implies ({
                         ||| old(self).gap(x, y)
                         ||| (old(self).gap(x, *lo) &&
                              old(self).gap(*hi, y) &&
                              (hi.geq_spec(y) || hi.is_end_spec() || !self@.contains_key(*hi.get())))
                        }) by {
            assert_by_contradiction!(
                             old(self).gap(x, y)
                         || (old(self).gap(x, *lo) &&
                             old(self).gap(*hi, y) &&
                             (hi.geq_spec(y) || hi.is_end_spec() || !self@.contains_key(*hi.get()))), {
                //assert(exists |ki| x.lt_spec(ki) && ki.lt_spec(y) && old(self)@.contains_key(*ki.get()));
                let ki = old(self).choose_gap_violator(x, y);
                if !old(self).gap(x, *lo) {
                    let kk = old(self).choose_gap_violator(x, *lo);
                    assert(self@.contains_key(*kk.get())); // contradicts self.gap(x, y)
                    K::cmp_properties();
                } else if !old(self).gap(*hi, y) {
                    let kk = old(self).choose_gap_violator(*hi, y);
                    assert(self@.contains_key(*kk.get())) by {   // contradicts self.gap(x, y)
                        K::cmp_properties();
                    };
                    K::cmp_properties();
                } else {
                    assert(!(hi.geq_spec(y) || hi.is_end_spec() || !self@.contains_key(*hi.get())));
                    assert(hi.lt_spec(y));
                    if x.lt_spec(*hi) {
                        self.gap_means_empty(x, y, *hi);
                    } else if x == hi {
                        self.gap_means_empty(*hi, ki, y);
                    } else {
                        assert(hi.lt_spec(x)) by { K::cmp_properties(); };
                        assert(self@.contains_key(*ki.get())) by { K::cmp_properties(); };
                    }
                }
                assert(self@.contains_key(*ki.get()));
            });
        }
        assert forall |x, y| ({
                         ||| old(self).gap(x, y)
                         ||| (old(self).gap(x, *lo) &&
                              old(self).gap(*hi, y) &&
                              (hi.geq_spec(y) || hi.is_end_spec() || !self@.contains_key(*hi.get())))
                        }) implies #[trigger] self.gap(x, y) by {
            if old(self).gap(x, y) {
                assert_by_contradiction!(self.gap(x, y), {
                    //let ki = self.choose_gap_violator(x, y);      // Flaky proof -- sometimes needs this line
                });
            }

            if old(self).gap(x, *lo) && old(self).gap(*hi, y) &&
               (hi.geq_spec(y) || hi.is_end_spec() || !self@.contains_key(*hi.get())) {
                assert forall |ki| x.lt_spec(ki) && ki.lt_spec(y) implies !(#[trigger] self@.contains_key(*ki.get())) by {
                    assert(KeyIterator::between(x, ki, y)) by { K::cmp_properties(); };
                    K::cmp_properties();      // Flaky
                    if ki.lt_spec(*lo) {
                        // flaky without assert_by_contradiction (and maybe still flaky)
                        assert_by_contradiction!(!(self@.contains_key(*ki.get())), {
                            assert(old(self)@.contains_key(*ki.get()));
                        });
                    } else if hi.lt_spec(ki) {
                        assert_by_contradiction!(!(self@.contains_key(*ki.get())), {
                            assert(old(self)@.contains_key(*ki.get()));
                        });
                    } else if ki == lo {
                        assert(!(self@.contains_key(*ki.get())));
                    } else if ki == hi {
                        assert(!(self@.contains_key(*ki.get())));
                    } else {
                        assert(KeyIterator::between(*lo, ki, *hi));
                    }
                    //old(self).mind_the_gap();
                };
            }
        }
    }
}

#[verifier::reject_recursive_types(K)]
pub struct DelegationMap<K: KeyTrait + VerusClone> {
    // Our efficient implementation based on ranges
    lows: StrictlyOrderedMap<K>,
    // Our spec version
    m: Ghost<Map<K, AbstractEndPoint>>,

}

pub struct EndPoint {
    pub id: Vec<u8>,
}

type ID = EndPoint;

pub trait KeyTrait : Sized {

    spec fn cmp_spec(self, other: Self) -> Ordering;

    proof fn cmp_properties()
        ensures
        // Equality is eq  --- TODO: Without this we need to redefine Seq, Set, etc. operators that use ==
        forall |a:Self, b:Self| #![auto] a == b <==> a.cmp_spec(b).eq(),
        // Reflexivity of equality
        forall |a:Self| #![auto] a.cmp_spec(a).eq(),
        // Commutativity of equality
        forall |a:Self, b:Self| (#[trigger] a.cmp_spec(b)).eq() == b.cmp_spec(a).eq(),
        // Transitivity of equality
        forall |a:Self, b:Self, c:Self|
            #[trigger] a.cmp_spec(b).eq() && #[trigger] b.cmp_spec(c).eq() ==> a.cmp_spec(c).eq(),
        // Inequality is asymmetric
        forall |a:Self, b:Self|
            #[trigger] a.cmp_spec(b).lt() <==> b.cmp_spec(a).gt(),
        // Connected
        forall |a:Self, b:Self|
            #![auto] a.cmp_spec(b).ne() ==> a.cmp_spec(b).lt() || b.cmp_spec(a).lt(),
        // Transitivity of inequality
        forall |a:Self, b:Self, c:Self|
            #[trigger] a.cmp_spec(b).lt() && #[trigger] b.cmp_spec(c).lt() ==> a.cmp_spec(c).lt(),
        forall |a:Self, b:Self, c:Self|
            #[trigger] a.cmp_spec(b).lt() && #[trigger] b.cmp_spec(c).le() ==> a.cmp_spec(c).lt(),
        forall |a:Self, b:Self, c:Self|
            #[trigger] a.cmp_spec(b).le() && #[trigger] b.cmp_spec(c).lt() ==> a.cmp_spec(c).lt();
}

pub enum Ordering {
    Less,
    Equal,
    Greater,
}

pub struct KeyIterator<K: KeyTrait + VerusClone> {
    // None means we hit the end
    pub k: Option<K>,
}

impl<K: KeyTrait + VerusClone> KeyIterator<K> {
    pub open spec fn new_spec(k: K) -> Self {
        KeyIterator { k: Some(k) }
    }

    pub open spec fn lt_spec(self, other: Self) -> bool {
        (!self.k.is_None() && other.k.is_None())
      || (!self.k.is_None() && !other.k.is_None() && self.k.get_Some_0().cmp_spec(other.k.get_Some_0()).lt())
    }

    pub open spec fn geq_spec(self, other: Self) -> bool {
        !self.lt_spec(other) //|| self == other
    }
}

pub trait VerusClone : Sized {}

}
