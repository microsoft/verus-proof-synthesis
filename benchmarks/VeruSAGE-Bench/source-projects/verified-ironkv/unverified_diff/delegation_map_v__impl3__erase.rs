use vstd::prelude::*;

fn main() {}

verus! {

pub trait VerusClone: Sized {}

pub struct EndPoint {
    pub id: Vec<u8>,
}

type ID = EndPoint;


pub enum Ordering {
    Less,
    Equal,
    Greater,
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

pub trait KeyTrait: Sized {
    spec fn cmp_spec(self, other: Self) -> Ordering;

    proof fn cmp_properties()
        ensures
            forall|a: Self, b: Self| #![auto] a == b <==> a.cmp_spec(b).eq(),
            forall|a: Self| #![auto] a.cmp_spec(a).eq(),
            forall|a: Self, b: Self| (#[trigger] a.cmp_spec(b)).eq() == b.cmp_spec(a).eq(),
            forall|a: Self, b: Self, c: Self| #[trigger]
                a.cmp_spec(b).eq() && #[trigger] b.cmp_spec(c).eq() ==> a.cmp_spec(c).eq(),
            forall|a: Self, b: Self| #[trigger] a.cmp_spec(b).lt() <==> b.cmp_spec(a).gt(),
            forall|a: Self, b: Self|
                #![auto]
                a.cmp_spec(b).ne() ==> a.cmp_spec(b).lt() || b.cmp_spec(a).lt(),
            forall|a: Self, b: Self, c: Self| #[trigger]
                a.cmp_spec(b).lt() && #[trigger] b.cmp_spec(c).lt() ==> a.cmp_spec(c).lt(),
            forall|a: Self, b: Self, c: Self| #[trigger]
                a.cmp_spec(b).lt() && #[trigger] b.cmp_spec(c).le() ==> a.cmp_spec(c).lt(),
            forall|a: Self, b: Self, c: Self| #[trigger]
                a.cmp_spec(b).le() && #[trigger] b.cmp_spec(c).lt() ==> a.cmp_spec(c).lt(),
    ;
}

spec fn sorted<K: KeyTrait>(s: Seq<K>) -> bool {
    forall|i, j| #![auto] 0 <= i < j < s.len() ==> s[i].cmp_spec(s[j]).lt()
}

pub struct KeyIterator<K: KeyTrait + VerusClone> {
    pub k: Option<K>,
}

impl<K: KeyTrait + VerusClone> KeyIterator<K> {
    pub open spec fn new_spec(k: K) -> Self {
        KeyIterator { k: Some(k) }
    }

    pub open spec fn lt_spec(self, other: Self) -> bool {
        (!self.k.is_None() && other.k.is_None()) || (!self.k.is_None() && !other.k.is_None()
            && self.k.get_Some_0().cmp_spec(other.k.get_Some_0()).lt())
    }

    pub open spec fn geq_spec(self, other: Self) -> bool {
        !self.lt_spec(other)
    }
}


impl<K: KeyTrait + VerusClone> KeyIterator<K> {
    pub open spec fn is_end_spec(&self) -> bool {
        self.k.is_None()
    }

    pub open spec fn get_spec(&self) -> &K
        recommends
            self.k.is_some(),
    {
        &self.k.get_Some_0()
    }

    spec fn above_spec(&self, k: K) -> bool {
        self.k.is_None() || k.cmp_spec(self.k.get_Some_0()).lt()
    }

    #[verifier::external_body]
    #[verifier(when_used_as_spec(above_spec))]
    fn above(&self, k: K) -> (b: bool)
        ensures
            b == self.above_spec(k),
    {
        unimplemented!()
    }

    pub open spec fn between(lhs: Self, ki: Self, rhs: Self) -> bool {
        !ki.lt_spec(lhs) && ki.lt_spec(rhs)
    }

    pub open spec fn end_spec() -> (s: Self) {
        KeyIterator { k: None }
    }

    #[verifier::external_body]
    #[verifier(when_used_as_spec(end_spec))]
    pub fn end() -> (s: Self)
        ensures
            s.k.is_None(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    #[verifier(when_used_as_spec(is_end_spec))]
    pub fn is_end(&self) -> (b: bool)
        ensures
            b == self.is_end_spec(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    #[verifier(when_used_as_spec(get_spec))]
    pub fn get(&self) -> (k: &K)
        requires
            !self.is_end(),
        ensures
            k == self.get_spec(),
    {
        unimplemented!()
    }
}


struct StrictlyOrderedVec<K: KeyTrait> {
    v: Vec<K>,
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
        requires
            self.valid(),
        ensures
            s == self@.to_set(),
            s.finite(),
            s.len() == self@.len(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    fn len(&self) -> (len: usize)
        ensures
            len == self@.len(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    fn index(&self, i: usize) -> (k: K)
        requires
            i < self@.len(),
        ensures
            k == self@[i as int],
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
            self@ == old(self)@.subrange(0, start as int) + old(self)@.subrange(
                end as int,
                old(self)@.len() as int,
            ),
            old(self)@.to_set() == self@.to_set() + old(self)@.subrange(
                start as int,
                end as int,
            ).to_set(),
    {
        unimplemented!()
    }
}

#[verifier::external_body]
pub fn vec_erase<A>(v: &mut Vec<A>, start: usize, end: usize)
    requires
        start <= end <= old(v).len(),
    ensures
        true,
        v@ == old(v)@.subrange(0, start as int) + old(v)@.subrange(
            end as int,
            old(v)@.len() as int,
        ),
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
    pub closed spec fn view(self) -> Map<K, ID> {
        self.m@
    }

    pub closed spec fn map_valid(self) -> bool {
        &&& self.m@.dom().finite()
        &&& self.m@.dom() == self.keys@.to_set()
        &&& forall|i|
            0 <= i < self.keys@.len() ==> #[trigger] (self.m@[self.keys@.index(i)])
                == self.vals@.index(i)
    }

    pub closed spec fn valid(self) -> bool {
        &&& self.keys.valid()
        &&& self.keys@.len() == self.vals.len()
        &&& self.map_valid()
    }

    spec fn gap(self, lo: KeyIterator<K>, hi: KeyIterator<K>) -> bool {
        forall|ki| lo.lt_spec(ki) && ki.lt_spec(hi) ==> !(#[trigger] self@.contains_key(*ki.get()))
    }

    #[verifier::external_body]
    proof fn gap_means_empty(self, lo: KeyIterator<K>, hi: KeyIterator<K>, k: KeyIterator<K>)
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
    proof fn choose_gap_violator(self, lo: KeyIterator<K>, hi: KeyIterator<K>) -> (r: KeyIterator<K>)
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
            forall|k|
                {
                    let ki = KeyIterator::new_spec(k);
                    (if ki.geq_spec(*lo) && ki.lt_spec(*hi) {
                        !(#[trigger] self@.contains_key(k))
                    } else {
                        (old(self)@.contains_key(k) ==> self@.contains_key(k) && self@[k] == old(
                            self,
                        )@[k]) && (self@.contains_key(k) ==> old(self)@.contains_key(k))
                    })
                },
            forall|x, y|
                self.gap(x, y) <==> ({
                    ||| old(self).gap(x, y)
                    ||| (old(self).gap(x, *lo) && old(self).gap(*hi, y) && (hi.geq_spec(y)
                        || hi.is_end_spec() || !self@.contains_key(*hi.get())))
                }),
    {
        let mut start = 0;
        while start < self.keys.len() && lo.above(self.keys.index(start)) {
            start = start + 1;
        }
        let mut end = start;
        while end < self.keys.len() && hi.above(self.keys.index(end)) {
            end = end + 1;
        }
        self.keys.erase(start, end);
        vec_erase(&mut self.vals, start, end);
        let ghost m_ghost: Map<K, ID> = arbitrary(); // TODO - replace with correct value
        self.m = Ghost(m_ghost);
    }
}

} // verus!
