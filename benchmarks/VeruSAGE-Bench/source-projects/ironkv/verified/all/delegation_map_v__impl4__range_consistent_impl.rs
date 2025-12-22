use vstd::prelude::*;
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

	#[verifier::external_body]
    pub fn is_eq(self) -> (b:bool)
        ensures b == self.eq(),
	{
		unimplemented!()
	}
    pub const fn is_lt(self) -> (b:bool)
        ensures b == self.lt(),
    {
        matches!(self, Ordering::Less)
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
    fn index(&self, i: usize) -> (k: K)
        requires i < self@.len(),
        ensures k == self@[i as int]
	{
		unimplemented!()
	}
}
impl<K: KeyTrait + VerusClone> KeyIterator<K> {

    pub open spec fn end_spec() -> (s: Self) {
        KeyIterator { k: None }
    }
    #[verifier(when_used_as_spec(end_spec))]
    pub fn end() -> (s: Self)
        ensures s.k.is_None()
    {
        KeyIterator { k: None }
    }


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
    fn keys_in_index_range_agree(&self, lo: usize, hi: usize, v: &ID) -> (ret:(bool, bool))
        requires 
            self.valid(),
            0 <= lo <= hi < self.keys@.len(),
        ensures 
            ret.0 == forall |i| #![auto] lo <= i <= hi ==> self@[self.keys@[i]]@ == v@,
            !ret.0 ==> (ret.1 == (self@[self.keys@[hi as int]]@ != v@ && (forall |i| #![auto] lo <= i < hi ==> self@[self.keys@[i]]@ == v@))),
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
    fn greatest_lower_bound_index(&self, iter: &KeyIterator<K>) -> (index: usize)
        requires
            self.valid(),
            self@.contains_key(K::zero_spec()),
        ensures
            0 <= index < self.keys@.len(),
            self.greatest_lower_bound_spec(*iter, KeyIterator::new_spec(self.keys@[index as int])),
	{
		unimplemented!()
	}
}

type ID = EndPoint;  // this code was trying to be too generic, but we need to know how to clone IDs. So we specialize.

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

    pub open spec fn range_consistent(self, lo: &KeyIterator<K>, hi: &KeyIterator<K>, dst: &ID) -> bool {
        forall |k| KeyIterator::between(*lo, KeyIterator::new_spec(k), *hi) ==> (#[trigger] self@[k]) == dst@
    }

	#[verifier::external_body]
    proof fn not_range_consistent(self, lo: &KeyIterator<K>, hi: &KeyIterator<K>, dst: &ID, bad: &KeyIterator<K>)
        requires
            KeyIterator::between(*lo, *bad, *hi),
            self@.contains_key(*bad.get()),
            self@[*bad.get()] != dst@,
        ensures
            !self.range_consistent(lo, hi, dst),
	{
		unimplemented!()
	}

	#[verifier::external_body]
    proof fn extend_range_consistent(self, x: &KeyIterator<K>, y: &KeyIterator<K>, z: &KeyIterator<K>, dst: &ID) 
        requires 
            self.range_consistent(x, y, dst),
            self.range_consistent(y, z, dst),
        ensures
            self.range_consistent(x, z, dst),
	{
		unimplemented!()
	}

	#[verifier::external_body]
    proof fn range_consistent_subset(self, x: &KeyIterator<K>, y: &KeyIterator<K>, x_inner: &KeyIterator<K>, y_inner: &KeyIterator<K>, dst: &ID) 
        requires 
            self.range_consistent(x, y, dst),
            x_inner.geq_spec(*x),
            !y.lt_spec(*y_inner),
        ensures
            self.range_consistent(x_inner, y_inner, dst),
	{
		unimplemented!()
	}

	#[verifier::external_body]
    proof fn empty_key_range_is_consistent(&self, lo: &KeyIterator<K>, hi: &KeyIterator<K>, id: &ID)
        requires
            lo.geq_spec(*hi),
        ensures 
            self.range_consistent(lo, hi, id),
	{
		unimplemented!()
	}

	#[verifier::external_body]
    proof fn all_keys_agree(&self, lo: usize, hi: usize, id: &ID)
        requires
            self.valid(),
            0 <= lo <= hi < self.lows.keys@.len(),
            forall |i| #![auto] lo <= i <= hi ==> self.lows@[self.lows.keys@[i]]@ == id@,
        ensures
            self.range_consistent(&KeyIterator::new_spec(self.lows.keys@[lo as int]), &KeyIterator::new_spec(self.lows.keys@[hi as int]), id),
        decreases hi - lo,
	{
		unimplemented!()
	}

	#[verifier::external_body]
    proof fn almost_all_keys_agree(&self, lo: usize, hi: usize, id: &ID)
        requires
            self.valid(),
            0 <= lo <= hi < self.lows.keys@.len(),
            forall |i| #![auto] lo <= i < hi ==> self.lows@[self.lows.keys@[i]]@ == id@,
        ensures
            self.range_consistent(&KeyIterator::new_spec(self.lows.keys@[lo as int]), &KeyIterator::new_spec(self.lows.keys@[hi as int]), id),
        decreases hi - lo,
	{
		unimplemented!()
	}

    pub fn range_consistent_impl(&self, lo: &KeyIterator<K>, hi: &KeyIterator<K>, dst: &ID) -> (b: bool)
        requires
            self.valid(),
        ensures
            b == self.range_consistent(lo, hi, dst),
    {
        if lo.lt(hi) {
            let lo_glb_index = self.lows.greatest_lower_bound_index(lo);
            let hi_glb_index = self.lows.greatest_lower_bound_index(hi);
            assert(lo_glb_index <= hi_glb_index) by {
                K::cmp_properties();
            };
            let ghost lo_glb = self.lows.keys@[lo_glb_index as int];
            let hi_glb = self.lows.keys.index(hi_glb_index);
            let ghost lo_glb_ki = KeyIterator::new_spec(lo_glb);
            let ghost hi_glb_ki = KeyIterator::new_spec(hi_glb);

            //let ret = self.lows.keys_agree(Ghost(&lo_glb), lo_glb_index, Ghost(&hi_glb), hi_glb_index, dst);
            let (agree, almost) = self.lows.keys_in_index_range_agree(lo_glb_index, hi_glb_index, dst);
            let ret = if agree {
                // Simple case where everything agrees
                true
            } else if !agree && almost && !hi.is_end() && hi_glb.cmp(hi.get()).is_eq() {
                // Corner case where almost everything agrees; the one disagreement
                // is exactly at the hi key, which isn't included in range_consistent
                true
            } else {
                // Simpler case where disagreement occurs before hi
                false
            };
            proof {
                let end_ki = KeyIterator::end_spec();
                if ret {
                    if agree {
                        self.all_keys_agree(lo_glb_index, hi_glb_index, dst);
                        if hi_glb_index == self.lows.keys@.len() - 1 {
                            assert forall |k| KeyIterator::between(hi_glb_ki, KeyIterator::new_spec(k), end_ki) implies (#[trigger] self@[k]) == dst@  by {
                                K::cmp_properties();
                            }
                            assert(self.range_consistent(&hi_glb_ki, &end_ki, dst));
                            self.extend_range_consistent(&lo_glb_ki, &hi_glb_ki, &end_ki, dst);
                            self.range_consistent_subset(&lo_glb_ki, &end_ki, lo, hi, dst);
                        } else {
                            let hi_next_index = hi_glb_index + 1;
                            let hi_next = self.lows.keys@[hi_next_index];
                            let hi_next_ki = KeyIterator::new_spec(hi_next);
                            assert(self.lows.gap(hi_glb_ki, hi_next_ki)) by {
                                K::cmp_properties();
                            }

                            assert_by_contradiction!(!hi.above(hi_next), {
                                K::cmp_properties();
                                assert(self.lows@.contains_key(hi_next));   // Trigger conclusion of glb_spec
                            });
                            assert(!hi.is_end_spec()) by {
                                K::cmp_properties();
                            }
                            let upper = choose |u| #[trigger] self.lows.gap(hi_glb_ki, u) && KeyIterator::between(hi_glb_ki, *hi, u);
                            assert(self.range_consistent(&hi_glb_ki, &upper, dst));
                            self.extend_range_consistent(&lo_glb_ki, &hi_glb_ki, &upper, dst);
                            assert(!upper.lt_spec(*hi)) by {
                                K::cmp_properties();
                            }
                            self.range_consistent_subset(&lo_glb_ki, &upper, lo, hi, dst);
                        }
                    } else {
                        assert(!agree && almost && !hi.is_end() && hi_glb.cmp_spec(*hi.get_spec()).eq());
                        self.almost_all_keys_agree(lo_glb_index, hi_glb_index, dst);
                        self.range_consistent(&KeyIterator::new_spec(self.lows.keys@[lo_glb_index as int]), 
                                              &KeyIterator::new_spec(self.lows.keys@[hi_glb_index as int]), dst);
                        assert(lo.geq_spec(lo_glb_ki));
                        self.range_consistent_subset(&lo_glb_ki, &hi_glb_ki, lo, hi, dst);
                    }
                } else {
                    assert(!agree);
                    let bad_index = choose |bad_index| #![auto] lo_glb_index <= bad_index <= hi_glb_index && self.lows@[self.lows.keys@[bad_index]]@ != dst@;
                    let bad = self.lows.keys@[bad_index];
                    let bad_ki = KeyIterator::new_spec(bad);

                    if bad_index == lo_glb_index {
                        let lo_k = *lo.get();
                        let upper = choose |u| #[trigger] self.lows.gap(lo_glb_ki, u) && KeyIterator::between(lo_glb_ki, KeyIterator::new_spec(lo_k), u);
                        assert(self.lows@.contains_key(lo_glb));
                        assert(self.lows.gap(KeyIterator::new_spec(lo_glb), upper));
                        assert(KeyIterator::between(KeyIterator::new_spec(lo_glb), KeyIterator::new_spec(lo_k), upper));
                        assert(self@[lo_k] == self.lows@[lo_glb]@);
                        assert(self.lows@[lo_glb]@ == self.lows@[self.lows.keys@[bad_index]]@);
                        assert(self@[lo_k] != dst@);
                        assert(KeyIterator::between(*lo, *lo, *hi)) by { K::cmp_properties(); }
                        self.not_range_consistent(lo, hi, dst, lo);
                    } else {

                        assert(hi.is_end_spec() ==> hi_glb_ki != hi);
                        assert(hi_glb_ki.cmp_spec(*hi).eq() == (hi_glb_ki == hi)) by { K::cmp_properties(); };

                        assert(bad_index > lo_glb_index && !bad_ki.lt_spec(*lo)) by { 
                            K::cmp_properties(); 
                            assert(self.lows@.contains_key(bad));   // Trigger conclusion of glb_spec
                        };

                        // almost == (self@[self.keys@[hi_glb_index as int]]@ != v@ &&
                        //            (forall |i| #![auto] lo_glb_index <= i < hi_glb_index ==> self@[self.keys@[i]]@ == v@)))
                        if almost {
                            assert(hi_glb_index == bad_index);
                            if !hi.is_end_spec() {
                                if hi_glb_ki == hi {
                                    assert(ret);
                                    assert(false);
                                } else {
                                    assert(KeyIterator::between(*lo, bad_ki, *hi)) by { K::cmp_properties(); };
                                    //assert(self.lows.gap(bad_ki, KeyIterator::new_spec(self.lows.keys@[bad_index + 1])));
                                    
                                    let upper = choose |u| #![auto] self.lows.gap(hi_glb_ki, u) && KeyIterator::between(hi_glb_ki, *hi, u);
                                    assert(self.lows@.contains_key(bad));
                                    //assert(self.lows.gap(bad_ki, upper));
                                    assert(self.lows.gap(bad_ki, *hi)) by { K::cmp_properties(); };
                                    assert(KeyIterator::between(hi_glb_ki, bad_ki, upper)) by { K::cmp_properties(); };
                                    assert(self@[bad] == self.lows@[bad]@);

                                    self.not_range_consistent(lo, hi, dst, &bad_ki);
                                }
                            } else {
                                if hi_glb_ki == hi {
                                    assert(false);
                                } else {
                                    assert(KeyIterator::between(*lo, bad_ki, *hi)) by { K::cmp_properties(); };
                                    //assert(self.lows.gap(bad_ki, KeyIterator::new_spec(self.lows.keys@[bad_index + 1])));
                                    
                                    //let upper = choose |u| #![auto] self.lows.gap(hi_glb_ki, u) && KeyIterator::between(hi_glb_ki, *hi, u);
                                    assert(self.lows@.contains_key(bad));
                                    //assert(self.lows.gap(bad_ki, upper));
                                    assert(self.lows.gap(bad_ki, *hi)) by { K::cmp_properties(); };
                                    assert(KeyIterator::between(hi_glb_ki, bad_ki, *hi)) by { K::cmp_properties(); };
                                    assert(self@[bad] == self.lows@[bad]@);

                                    self.not_range_consistent(lo, hi, dst, &bad_ki);
                                }
                            }
                        } else {
                            assert(self.lows@[self.lows.keys@[hi_glb_index as int]]@ == dst@ ||
                                    !(forall |i| #![auto] lo_glb_index <= i < hi_glb_index ==> self.lows@[self.lows.keys@[i]]@ == dst@));

                            if self.lows@[self.lows.keys@[hi_glb_index as int]]@ == dst@ {
                                if !hi.is_end_spec() {
                                    if hi_glb_ki == hi {
                                        assert(bad_index < hi_glb_index);
                                        // Proof X
                                        let bad_next = self.lows.keys@[bad_index+1];
                                        let bad_next_ki = KeyIterator::new_spec(bad_next);
                                        assert(KeyIterator::between(*lo, bad_ki, *hi)) by { K::cmp_properties(); }
                                        assert(self@[bad] != dst@) by {
                                            // Trigger DelegationMap::valid
                                            assert(self.lows.gap(bad_ki, bad_next_ki)) by { K::cmp_properties(); };
                                            assert(KeyIterator::between(bad_ki, bad_ki, bad_next_ki)) by { K::cmp_properties(); };
                                        }
                                        self.not_range_consistent(lo, hi, dst, &bad_ki);
                                    } else {
                                        // TODO: Duplicates entire Proof Y
                                        if bad_index < hi_glb_index {
                                            // TODO: This duplicates Proof X 
                                            assert(bad_index+1 < self.lows.keys@.len());
                                            let bad_next = self.lows.keys@[bad_index+1];
                                            let bad_next_ki = KeyIterator::new_spec(bad_next);
                                            assert(KeyIterator::between(*lo, bad_ki, *hi)) by { K::cmp_properties(); }
                                            assert(self@[bad] != dst@) by {
                                                // Trigger DelegationMap::valid
                                                assert(self.lows.gap(bad_ki, bad_next_ki)) by { K::cmp_properties(); };
                                                assert(KeyIterator::between(bad_ki, bad_ki, bad_next_ki)) by { K::cmp_properties(); };
                                            }
                                            self.not_range_consistent(lo, hi, dst, &bad_ki);
                                        } else {
                                            // From glb_spec:
                                            let upper = choose |u| #![auto] self.lows.gap(hi_glb_ki, u) && KeyIterator::between(hi_glb_ki, *hi, u);
                                            assert(self@[hi_glb] == self.lows@[hi_glb]@) by {
                                                assert(self.lows@.contains_key(hi_glb));
                                                assert(self.lows.gap(hi_glb_ki, upper) && KeyIterator::between(hi_glb_ki, *hi, upper));
                                                assert(KeyIterator::between(hi_glb_ki, hi_glb_ki, upper)) by { K::cmp_properties(); };   // Trigger: DelegationMap::valid()
                                            }
                                            self.not_range_consistent(lo, hi, dst, &bad_ki);
                                        }

                                    }
                                } else {
                                    if hi_glb_ki == hi {
                                        assert(false);
                                    } else {
                                        // Proof Y
                                        if bad_index < hi_glb_index {
                                            // TODO: This duplicates Proof X 
                                            assert(bad_index+1 < self.lows.keys@.len());
                                            let bad_next = self.lows.keys@[bad_index+1];
                                            let bad_next_ki = KeyIterator::new_spec(bad_next);
                                            assert(KeyIterator::between(*lo, bad_ki, *hi)) by { K::cmp_properties(); }
                                            assert(self@[bad] != dst@) by {
                                                // Trigger DelegationMap::valid
                                                assert(self.lows.gap(bad_ki, bad_next_ki)) by { K::cmp_properties(); };
                                                assert(KeyIterator::between(bad_ki, bad_ki, bad_next_ki)) by { K::cmp_properties(); };
                                            }
                                            self.not_range_consistent(lo, hi, dst, &bad_ki);
                                        } else {
                                            // From glb_spec:
                                            let upper = choose |u| #![auto] self.lows.gap(hi_glb_ki, u) && KeyIterator::between(hi_glb_ki, *hi, u);
                                            assert(self@[hi_glb] == self.lows@[hi_glb]@) by {
                                                assert(self.lows@.contains_key(hi_glb));
                                                assert(self.lows.gap(hi_glb_ki, upper) && KeyIterator::between(hi_glb_ki, *hi, upper));
                                                assert(KeyIterator::between(hi_glb_ki, hi_glb_ki, upper)) by { K::cmp_properties(); };   // Trigger: DelegationMap::valid()
                                            }
                                            self.not_range_consistent(lo, hi, dst, &bad_ki);
                                        }
                                    }
                                }

                            }

                            if !(forall |i:int| lo_glb_index <= i < hi_glb_index ==> #[trigger](self.lows@[self.lows.keys@[i]]@) == dst@) {
                                // Choose a badder index
                                let bad_index = choose |bad_index| #![auto] lo_glb_index <= bad_index < hi_glb_index && self.lows@[self.lows.keys@[bad_index]]@ != dst@;
                                let bad = self.lows.keys@[bad_index];
                                let bad_ki = KeyIterator::new_spec(bad);

                                if bad_index == lo_glb_index {
                                    // TODO: Duplicates proof above
                                    let lo_k = *lo.get();
                                    let upper = choose |u| #[trigger] self.lows.gap(lo_glb_ki, u) && KeyIterator::between(lo_glb_ki, KeyIterator::new_spec(lo_k), u);
                                    assert(self.lows@.contains_key(lo_glb));
                                    assert(self.lows.gap(KeyIterator::new_spec(lo_glb), upper));
                                    assert(KeyIterator::between(KeyIterator::new_spec(lo_glb), KeyIterator::new_spec(lo_k), upper));
                                    assert(self@[lo_k] == self.lows@[lo_glb]@);
                                    assert(self.lows@[lo_glb]@ == self.lows@[self.lows.keys@[bad_index]]@);
                                    assert(self@[lo_k] != dst@);
                                    assert(KeyIterator::between(*lo, *lo, *hi)) by { K::cmp_properties(); }
                                    self.not_range_consistent(lo, hi, dst, lo);
                                } else {
                                    // TODO: This duplicates Proof X 
                                    assert(bad_index+1 < self.lows.keys@.len());
                                    let bad_next = self.lows.keys@[bad_index+1];
                                    let bad_next_ki = KeyIterator::new_spec(bad_next);
                                    assert(KeyIterator::between(*lo, bad_ki, *hi)) by { 
                                        K::cmp_properties(); 
                                        assert(self.lows@.contains_key(bad));   // Trigger conclusion of glb_spec
                                    }
                                    assert(self@[bad] != dst@) by {
                                        // Trigger DelegationMap::valid
                                        assert(self.lows.gap(bad_ki, bad_next_ki)) by { K::cmp_properties(); };
                                        assert(KeyIterator::between(bad_ki, bad_ki, bad_next_ki)) by { K::cmp_properties(); };
                                    }
                                    self.not_range_consistent(lo, hi, dst, &bad_ki);
                                }
                            }

                        }
                    }
                }
            }
            ret
        } else {
            proof {
                self.empty_key_range_is_consistent(lo, hi, dst);
            }
            true
        }
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

    pub open spec fn cmp_spec(self, other: Self) -> Ordering {
        match (self.k, other.k) {
            (None, None) => Ordering::Equal,
            (None, Some(_)) => Ordering::Less,
            (Some(_), None) => Ordering::Greater,
            (Some(i), Some(j)) => { i.cmp_spec(j) }
        }
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
