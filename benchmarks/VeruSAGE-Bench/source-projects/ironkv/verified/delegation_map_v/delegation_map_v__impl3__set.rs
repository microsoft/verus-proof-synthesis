use vstd::prelude::*;
use vstd::assert_by_contradiction;
use vstd::set_lib::*;

fn main() {}

verus! {

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
    fn insert(&mut self, k: K) -> (i: usize)
        requires
            old(self).valid(),
            !old(self)@.contains(k),
        ensures self.valid(),
            self@.len() == old(self)@.len() + 1,
            0 <= i < self@.len(),
            self@ == old(self)@.insert(i as int, k),
            self@.to_set() == old(self)@.to_set().insert(k),
	{
		unimplemented!()
	}
}

impl<K: KeyTrait + VerusClone> KeyIterator<K> {

    pub open spec fn get_spec(&self) -> &K
        recommends self.k.is_some(),
    {
        &self.k.get_Some_0()
    }

    #[verifier::external_body]
    #[verifier(when_used_as_spec(get_spec))]
    pub fn get(&self) -> (k: &K)
        requires !self.is_end(),
        ensures k == self.get_spec(),
    {
        unimplemented!()
    }
    pub open spec fn is_end_spec(&self) -> bool {
        self.k.is_None()
    }

    #[verifier::external_body]
    #[verifier(when_used_as_spec(is_end_spec))]
    pub fn is_end(&self) -> (b: bool)
        ensures b == self.is_end_spec()
    {
        unimplemented!()
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
    fn find_key(&self, k: &K) -> (o: Option<usize>)
        requires self.valid(),
        ensures
            match o {
                None => !self@.contains_key(*k),
                Some(i) => 0 <= i < self.keys@.len() && self.keys@[i as int] == k,
        },
	{
		unimplemented!()
	}

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
        match self.find_key(&k) {
            Some(i) => {
                self.vals.set(i, v);
                self.m = Ghost(self.m@.insert(k, v));
                proof {
                    assert_sets_equal!(self.m@.dom() == self.keys@.to_set());
                }
            },
            None => {
                let index = self.keys.insert(k.clone());
                self.vals.insert(index, v);
                self.m = Ghost(self.m@.insert(k, v));
            }
        }
        assert forall |lo, hi| self.gap(lo, hi) <==>
                            old(self).gap(lo, hi)
                        && !(lo.lt_spec(KeyIterator::new_spec(k))
                          && KeyIterator::new_spec(k).lt_spec(hi)) by {
            self.mind_the_gap();
            old(self).mind_the_gap();
            if old(self).gap(lo, hi) && !(lo.lt_spec(KeyIterator::new_spec(k)) && KeyIterator::new_spec(k).lt_spec(hi)) {
                assert forall |ki| lo.lt_spec(ki) && ki.lt_spec(hi) implies !(#[trigger] self@.contains_key(*ki.get())) by {
                    // TODO: This was the previous (flaky) proof:
                    // K::cmp_properties();
                    //
                    assert_by_contradiction!(!old(self)@.contains_key(*ki.get()), {
                        old(self).gap_means_empty(lo, hi, ki);
                    });
                };
                assert(self.gap(lo, hi));
            }

            if self.gap(lo, hi) {
                assert forall |ki| lo.lt_spec(ki) && ki.lt_spec(hi) implies !(#[trigger] old(self)@.contains_key(*ki.get())) by {
                    assert_by_contradiction!(!(old(self)@.contains_key(*ki.get())), {
                        assert(self@.contains_key(*ki.get()));
                        K::cmp_properties();
                    });
                };
                assert(old(self).gap(lo, hi));
                assert_by_contradiction!(!(lo.lt_spec(KeyIterator::new_spec(k)) && KeyIterator::new_spec(k).lt_spec(hi)), {
                    assert(self@.contains_key(k));
                    self.gap_means_empty(lo, hi, KeyIterator::new_spec(k));
                });
            }
        };
    }
}

type ID = EndPoint ;

pub struct EndPoint {
    pub id: Vec<u8>,
}


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

pub trait VerusClone : Sized {
    fn clone(&self) -> (o: Self) 
        ensures o == self;
}

}
