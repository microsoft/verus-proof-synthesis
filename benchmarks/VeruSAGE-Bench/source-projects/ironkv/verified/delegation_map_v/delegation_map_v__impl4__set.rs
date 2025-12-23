use vstd::prelude::*;
use vstd::set_lib::*;
use vstd::assert_by_contradiction;

fn main() {}

verus! {

pub struct AbstractEndPoint {
    pub id: Seq<u8>,
}

impl AbstractEndPoint{
    pub open spec fn valid_physical_address(self) -> bool {
        self.id.len() < 0x100000
    }

}

impl Ordering{
    pub const fn is_lt(self) -> (b:bool)
        ensures b == self.lt(),
    {
        matches!(self, Ordering::Less)
    }

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
}

impl<K: KeyTrait + VerusClone> KeyIterator<K> {

    pub open spec fn is_end_spec(&self) -> bool {
        self.k.is_None()
    }

    #[verifier(when_used_as_spec(is_end_spec))]
    pub fn is_end(&self) -> (b: bool)
        ensures b == self.is_end_spec()
    {
        matches!(self.k, None)
    }


    pub open spec fn get_spec(&self) -> &K
        recommends self.k.is_some(),
    {
        &self.k.get_Some_0()
    }

    #[verifier(when_used_as_spec(get_spec))]
    pub fn get(&self) -> (k: &K)
        requires !self.is_end(),
        ensures k == self.get_spec(),
    {
        self.k.as_ref().unwrap()
    }

	#[verifier::external_body]
   pub fn lt(&self, other: &Self) -> (b: bool)
        ensures b == self.lt_spec(*other),
	{
		unimplemented!()
	}

    spec fn above_spec(&self, k: K) -> bool {
        self.k.is_None() || k.cmp_spec(self.k.get_Some_0()).lt()
    }
    #[verifier(when_used_as_spec(above_spec))]
    fn above(&self, k: K) -> (b: bool)
        ensures b == self.above_spec(k),
    {
        self.is_end() || k.cmp(&self.k.as_ref().unwrap().clone()).is_lt()
    }


    pub open spec fn between(lhs: Self, ki: Self, rhs: Self) -> bool {
        !ki.lt_spec(lhs) && ki.lt_spec(rhs)
    }
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
    proof fn mind_the_gap(self)
        ensures
            forall|w, x, y, z| self.gap(w, x) && self.gap(y, z) && #[trigger] y.lt_spec(x) ==> #[trigger] self.gap(w, z),
            forall|w, x, y: KeyIterator<K>, z| #[trigger] self.gap(w, x) && y.geq_spec(w) && x.geq_spec(z) ==> #[trigger] self.gap(y, z),
            forall|l:KeyIterator<K>, k, m| #[trigger] self.gap(k, m) ==> !(k.lt_spec(l) && l.lt_spec(m) && #[trigger] self@.contains_key(*l.get()))
	{
		unimplemented!()
	}

	#[verifier::external_body]
    fn set(&mut self, k: K, v: ID)
        requires
            old(self).valid(),
        ensures
            self.valid(),
            self@ == old(self)@.insert(k, v),
            forall |lo, hi| self.gap(lo, hi) <==>
                            old(self).gap(lo, hi)
                        && !(lo.lt_spec(KeyIterator::new_spec(k))
                          && KeyIterator::new_spec(k).lt_spec(hi)),
	{
		unimplemented!()
	}

    spec fn greatest_lower_bound_spec(self, iter: KeyIterator<K>, glb: KeyIterator<K>) -> bool {
        (glb == iter || glb.lt_spec(iter)) &&
        (forall|k| KeyIterator::new_spec(k) != glb && #[trigger] self@.contains_key(k) && iter.above(k) ==> glb.above(k)) &&
        (!iter.is_end_spec() ==>
            glb.k.is_Some() &&
            self@.contains_key(glb.k.get_Some_0()) &&
            // There are no keys in the interval (glb, hi), and iter falls into that gap
            (exists|hi| #[trigger] self.gap(glb, hi) && #[trigger] KeyIterator::between(glb, iter, hi)))
    }

	#[verifier::external_body]
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
		unimplemented!()
	}
}

#[verifier::reject_recursive_types(K)]

pub struct DelegationMap<K: KeyTrait + VerusClone> {
    // Our efficient implementation based on ranges
    lows: StrictlyOrderedMap<K>,
    // Our spec version
    m: Ghost<Map<K, AbstractEndPoint>>,

}
impl<K: KeyTrait + VerusClone> DelegationMap<K> {

    pub closed spec fn view(self) -> Map<K,AbstractEndPoint> {
        self.m@
    }

    pub closed spec fn valid(self) -> bool {
        &&& self.lows.valid()
        &&& self.lows@.contains_key(K::zero_spec())
        &&& self@.dom().is_full()
        &&& (forall|k| #[trigger] self@[k].valid_physical_address())
        &&& (forall|k, i, j|
                      self.lows@.contains_key(i)
                   && self.lows.gap(KeyIterator::new_spec(i), j)
                   && #[trigger] KeyIterator::between(KeyIterator::new_spec(i), KeyIterator::new_spec(k), j)
                   ==> self@[k] == self.lows@[i]@)
    }

	#[verifier::external_body]
    fn get_internal(&self, k: &K) -> (res: (ID, Ghost<KeyIterator<K>>))
        requires
            self.valid(),
        ensures ({
            let (id, glb) = res;
            &&& id@ == self@[*k]
            &&& self.lows.greatest_lower_bound_spec(KeyIterator::new_spec(*k), glb@)
            &&& id@.valid_physical_address()
    }),
	{
		unimplemented!()
	}

    pub fn set(&mut self, lo: &KeyIterator<K>, hi: &KeyIterator<K>, dst: &ID)
        requires
            old(self).valid(),
            dst@.valid_physical_address(),
        ensures
            self.valid(),
            forall |ki:KeyIterator<K>| #[trigger] KeyIterator::between(*lo, ki, *hi) ==> self@[*ki.get()] == dst@,
            forall |ki:KeyIterator<K>| !ki.is_end_spec() && !(#[trigger] KeyIterator::between(*lo, ki, *hi)) ==> self@[*ki.get()] == old(self)@[*ki.get()],
    {
        if lo.lt(&hi) {
            let ghost mut glb;
            if !hi.is_end() {
                // Get the current value of hi
                let (id, glb_ret) = self.get_internal(hi.get());
                proof { glb = glb_ret@; }
                // Set it explicitly
                self.lows.set(hi.get().clone(), id);
            }
            let ghost mut pre_erase; proof { pre_erase = self.lows@; }
            let ghost mut pre_erase_vec; proof { pre_erase_vec = self.lows; }
            self.lows.erase(&lo, &hi);
            let ghost mut erased; proof { erased = self.lows@; }
            let ghost mut erased_vec; proof { erased_vec = self.lows; }
            self.lows.set(lo.get().clone(), clone_end_point(dst));
            self.m = Ghost(self.m@.union_prefer_right(
                        Map::new(|k| KeyIterator::between(*lo, KeyIterator::new_spec(k), *hi),
                                 |k| dst@)));
            assert(self@.dom().is_full()) by {
                assert_sets_equal!(self@.dom(), Set::full());
            }
            assert (self.lows@.contains_key(K::zero_spec())) by {
                let ki = KeyIterator::new_spec(K::zero_spec());
                assert_by_contradiction!(!lo.lt_spec(ki), {
                    K::zero_properties();
                    K::cmp_properties();
                });
                if lo == ki {
                } else {
                    assert(ki.lt_spec(*lo)) by {
                        K::zero_properties();
                    }
                }
            };
            assert forall |k, i, j|
                        self.lows@.contains_key(i)
                   && self.lows.gap(KeyIterator::new_spec(i), j)
                   && #[trigger] KeyIterator::between(KeyIterator::new_spec(i), KeyIterator::new_spec(k), j)
                   implies self@[k] == self.lows@[i]@ by {
                let ii = KeyIterator::new_spec(i);
                let ki = KeyIterator::new_spec(k);
                if KeyIterator::between(*lo, ki, *hi) {
                    assert(self@[k] == dst@);
                    assert_by_contradiction!(ii == lo, {
                        if lo.lt_spec(ii) {
                            K::cmp_properties();
                        } else {
                            K::cmp_properties();
                            assert(ii.lt_spec(*lo));
                            // We have ii < lo < hi && ii <= k < j, and nothing in (ii, j)
                            // and lo <= k < hi
                            // ==> ii < lo <= k < j
                            assert(lo.lt_spec(j));
                            assert(!self.lows@.contains_key(*lo.get()));    // OBSERVE
                        }
                    });
                    assert(self.lows@[i]@ == dst@);
                } else if ki.lt_spec(*lo) {
                    assert(self@[k] == old(self)@[k]);
                    assert(!(ki.geq_spec(*lo) && ki.lt_spec(*hi)));
                    assert(erased.contains_key(i));
                    assert(ii != hi) by { K::cmp_properties(); };
                    assert(old(self).lows@.contains_key(i));
                    assert(self.lows@[i] == old(self).lows@[i]);
                    assert(old(self).lows.gap(ii, j)) by {
                        assert_by_contradiction!(!lo.lt_spec(j), {
                            K::cmp_properties();
                            assert(!self.lows@.contains_key(*lo.get()));    // OBSERVE
                        });
                        // TODO: add a trigger annotation once https://github.com/verus-lang/verus/issues/335 is fixed
                        assert forall |m| KeyIterator::new_spec(m).lt_spec(*lo) implies
                            (old(self).lows@.contains_key(m) ==
                                  #[trigger] self.lows@.contains_key(m)) by {
                            K::cmp_properties();
                        };
                        // TODO: add a trigger annotation once https://github.com/verus-lang/verus/issues/335 is fixed
                        assert forall |mi| ii.lt_spec(mi) && mi.lt_spec(j)
                            implies !(#[trigger] old(self).lows@.contains_key(*mi.get())) by {
                            K::cmp_properties();
                        }
                    };
                    assert(old(self)@[k] == old(self).lows@[i]@);
                } else {
                    // We have:
                    //   self.lows@.contains i
                    //   nothing in (i, j)
                    //   i < k < j
                    //   lo < hi <= k < j
                    assert(ki.geq_spec(*hi));
                    assert(self@[k] == old(self)@[k]);
                    assert(!hi.is_end());

                    assert((ii != hi && old(self)@[k] == old(self).lows@[i]@) || self@[k] == self.lows@[i]@) by {
                        assert((ii != hi && old(self).lows@.contains_key(i)) || ii == hi) by {
                            assert_by_contradiction!(!ii.lt_spec(*lo), {
                                // Flaky proof here
                                K::cmp_properties();
                            });

                            assert_by_contradiction!(ii != lo, {
                                // We need the following to prove hi is in self.lows@
                                assert(!hi.lt_spec(*hi)) by { K::cmp_properties(); };
                                assert(pre_erase.contains_key(*hi.get()));
                                assert(erased.contains_key(*hi.get()));
                                assert(self.lows@.contains_key(*hi.get()));

                                // But we have i < hi < j
                                assert(hi.lt_spec(j)) by { K::cmp_properties(); };

                                // which violates lows.gap(i, j)
                                //assert(false);
                            });

                            assert(lo.lt_spec(ii)) by { K::cmp_properties(); };
                            // lo < i ==>
                            // lo < i <= k < j
                            // lo < hi <= k < j
                            assert_by_contradiction!(!ii.lt_spec(*hi), {
                                // If this were true, we would have i < hi < j,
                                // which violates gap(i, j)
                                assert(hi.lt_spec(j)) by { K::cmp_properties(); };
                                //assert(false);
                            });
                            // Therefore hi <= i
                            if ii == hi {
                            } else {
                                // hi < i   ==> keys from i to j in lows didn't change
                                assert(erased.contains_key(i));
                                assert(pre_erase.contains_key(i));
                                assert(old(self).lows@.contains_key(i));
//                                assert forall |m| ii.lt_spec(m) && m.lt_spec(j)
//                                        implies !(#[trigger] old(self)@.contains_key(*m.get())) by {
//                                    K::cmp_properties();
////                                    assert_by_contradiction!(!old(self)@.contains_key(*m.get()), {
////                                        K::cmp_properties();
////                                        assert(self@.contains_key(*m.get()));
////                                        assert(KeyIterator::between(ii, m, j));
////                                        self.lows.gap_means_empty(ii, j, m);
////                                    });
//                                };
                                K::cmp_properties();    // Flaky
                                assert(old(self).lows.gap(KeyIterator::new_spec(i), j));
                            }
                        };

                        //assert(erased.gap(i, j));

                        if ii == hi {
                            //   lo < (hi == i) < k < j
                            assert(pre_erase[*hi.get()]@ == old(self)@[*hi.get()]);
                            assert(erased[*hi.get()] == pre_erase[*hi.get()]) by { K::cmp_properties(); };
                            assert(self@[*hi.get()] == erased[*hi.get()]@);
                            // Above establishes self@[*hi.get()] == old(self)@[*hi.get()]
                            assert(erased_vec.gap(ii, j));
                            assert(pre_erase_vec.gap(ii, j));
                            assert(old(self).lows.gap(ii, j));
                            if old(self).lows@.contains_key(i) {
                                assert(old(self)@[k] == old(self).lows@[i]@);
                            } else {
                                // old(self) did not contain hi; instead we added it inside the `if !hi.is_end()` clause
                                // But we know that glb was the closest bound to hi and glb is in old(self).lows@
                                assert(old(self).lows@.contains_key(*glb.get()));
                                assert(old(self).lows@[*glb.get()]@ == pre_erase[*hi.get()]@);
                                assert_by_contradiction!(!ii.lt_spec(glb), {
                                    K::cmp_properties();
                                });
                                assert(ii.geq_spec(glb));
                                // Establish the preconditions to use @old(self).valid() to relate
                                // old(self)@[k] to old(self).lows@[glb]
                                let hi_hi = choose |h| #[trigger] old(self).lows.gap(glb, h) && KeyIterator::between(glb, *hi, h);
                                assert(old(self).lows.gap(glb, j)) by { old(self).lows.mind_the_gap(); }
                                assert(KeyIterator::between(glb, ki, j)) by { K::cmp_properties(); };
                                assert(old(self)@[k] == old(self).lows@[*glb.get()]@);

                                // Directly prove that  self@[k] == self.lows@[i]
                                assert(old(self).lows@[*glb.get()]@ == pre_erase[*hi.get()]@);
                                assert(old(self).lows@[*glb.get()]@ == self@[*hi.get()]);
                                assert(old(self)@[k] == self@[*hi.get()]);
                                assert(self@[k] == self@[*hi.get()]);
                                assert(*lo.get() != i) by { K::cmp_properties(); };
                                assert(self.lows@[i] == erased[i]);
                                assert(self@[*hi.get()] == self.lows@[i]@);
                                assert(self@[k] == self.lows@[i]@);
                            }
                        } else {
                            assert(old(self).lows@.contains_key(i));
                            assert(erased_vec.gap(KeyIterator::new_spec(i), j));
                            // Prove that we can't be in the second clause of erase's gap
                            // postcondition
                            assert_by_contradiction!(!(hi.geq_spec(j) ||
                                                       hi.is_end_spec() ||
                                                       !erased_vec@.contains_key(*hi.get())), {
                                K::cmp_properties();
                            });
                            // Therefore we must be in the first clause, and hence:
                            assert(pre_erase_vec.gap(KeyIterator::new_spec(i), j));
                            assert(old(self).lows.gap(KeyIterator::new_spec(i), j));
                        }
                    };

                    if ii != hi {
                        assert(erased.contains_key(i)) by { K::cmp_properties(); };
                        assert(self.lows@[i] == erased[i]) by { K::cmp_properties(); };
                        assert(pre_erase.contains_key(i)) by { K::cmp_properties(); };
                        assert(erased[i] == pre_erase[i]);
                        assert(old(self).lows@.contains_key(i));
                        assert(old(self).lows@[i] == pre_erase[i]);
                        assert(old(self).lows@[i] == pre_erase[i]);
                        assert(self.lows@[i] == old(self).lows@[i]);
                    }
                }
            }
        }
        assert forall |ki:KeyIterator<K>| #[trigger] KeyIterator::between(*lo, ki, *hi) implies self@[*ki.get()] == dst@ by {
            K::cmp_properties();
        };
        // TODO: add a trigger annotation once https://github.com/verus-lang/verus/issues/335 is fixed
        assert forall |ki:KeyIterator<K>| !ki.is_end_spec() && !(#[trigger] KeyIterator::between(*lo, ki, *hi))
                                          implies self@[*ki.get()] == old(self)@[*ki.get()] by {
            K::cmp_properties();
        };
    }

}


pub struct EndPoint {
    pub id: Vec<u8>,
}

impl EndPoint{

    pub open spec fn view(self) -> AbstractEndPoint {
        AbstractEndPoint{id: self.id@}
    }

}

pub trait KeyTrait : Sized {

    spec fn zero_spec() -> Self where Self: std::marker::Sized;

    proof fn zero_properties()
        ensures
            forall |k:Self| k != Self::zero_spec() ==> (#[trigger] Self::zero_spec().cmp_spec(k)).lt();

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

    fn cmp(&self, other: &Self) -> (o: Ordering)
        requires true,
        ensures o == self.cmp_spec(*other);

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

pub trait VerusClone : Sized {
     fn clone(&self) -> (o: Self)
        ensures o == self;
}

type ID = EndPoint;


	#[verifier::external_body]
    pub fn clone_end_point(ep: &EndPoint) -> (cloned_ep: EndPoint)
        ensures
            cloned_ep@ == ep@
	{
		unimplemented!()
	}

}
