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

    #[verifier::external_body]
    pub const fn is_lt(self) -> (b: bool)
        ensures
            b == self.lt(),
    {
        unimplemented!()
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

    fn cmp(&self, other: &Self) -> (o: Ordering)
        requires
            true,
        ensures
            o == self.cmp_spec(*other),
    ;
}

spec fn sorted<K: KeyTrait>(s: Seq<K>) -> bool {
    forall|i, j| #![auto] 0 <= i < j < s.len() ==> s[i].cmp_spec(s[j]).lt()
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

    fn insert(&mut self, k: K) -> (i: usize)
        requires
            old(self).valid(),
            !old(self)@.contains(k),
        ensures
            self.valid(),
            self@.len() == old(self)@.len() + 1,
            0 <= i < self@.len(),
            self@ == old(self)@.insert(i as int, k),
            self@.to_set() == old(self)@.to_set().insert(k),
    {
        let mut index: usize = 0;
        while index < self.v.len() && self.v[index].cmp(&k).is_lt() {
            index = index + 1;
        }
        self.v.insert(index, k);
        return index;
    }
}

} // verus!
