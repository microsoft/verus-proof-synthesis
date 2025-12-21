extern crate verus_builtin_macros as builtin_macros;
use std::collections;
use vstd::bytes::*;
use vstd::prelude::*;
fn main() {}
verus! {

#[verifier(external_body)]
pub struct CKeyHashMap {
    m: collections::HashMap<CKey, Vec<u8>>,
}

impl CKeyHashMap {
    pub uninterp spec fn view(self) -> Map<AbstractKey, Seq<u8>>;

    pub uninterp spec fn spec_to_vec(&self) -> Vec<CKeyKV>;

    #[verifier(external_body)]
    #[verifier(when_used_as_spec(spec_to_vec))]
    pub fn to_vec(&self) -> (res: Vec<CKeyKV>) {
        unimplemented!()
    }

    pub uninterp spec fn spec_from_vec(v: Vec<CKeyKV>) -> Self;
}

pub struct CKeyKV {
    pub k: CKey,
    pub v: Vec<u8>,
}

impl CKeyKV {
    pub open spec fn view(self) -> (AbstractKey, Seq<u8>) {
        (self.k, self.v@)
    }
}

pub open spec fn ckeykvlt(a: CKeyKV, b: CKeyKV) -> bool {
    a.k.ukey < b.k.ukey
}

pub open spec fn spec_sorted_keys(v: Vec<CKeyKV>) -> bool {
    forall|i: int, j: int|
        0 <= i && i + 1 < v.len() && j == i + 1 ==> #[trigger] ckeykvlt(v@[i], v@[j])
}

#[derive(Eq, PartialEq, Hash)]
pub struct SHTKey {
    pub ukey: u64,
}

pub trait Marshalable: Sized {
    spec fn is_marshalable(&self) -> bool;

    #[verifier::external_body]
    spec fn ghost_serialize(&self) -> Seq<u8>
        recommends
            self.is_marshalable(),
    {
        unimplemented!()
    }
}

impl Marshalable for u64 {
    open spec fn is_marshalable(&self) -> bool {
        true
    }

    open spec fn ghost_serialize(&self) -> Seq<u8> {
        spec_u64_to_le_bytes(*self)
    }
}

impl Marshalable for usize {
    open spec fn is_marshalable(&self) -> bool {
        &&& *self as int <= u64::MAX
    }

    open spec fn ghost_serialize(&self) -> Seq<u8> {
        (*self as u64).ghost_serialize()
    }
}

impl Marshalable for Vec<u8> {
    open spec fn is_marshalable(&self) -> bool {
        self@.len() <= usize::MAX && (self@.len() as usize).ghost_serialize().len()
            + self@.len() as int <= usize::MAX
    }

    open spec fn ghost_serialize(&self) -> Seq<u8> {
        (self@.len() as usize).ghost_serialize() + self@
    }
}

impl<T: Marshalable> Marshalable for Vec<T> {
    open spec fn is_marshalable(&self) -> bool {
        &&& self@.len() <= usize::MAX
        &&& (forall|x: T| self@.contains(x) ==> #[trigger] x.is_marshalable())
        &&& (self@.len() as usize).ghost_serialize().len() + self@.fold_left(
            0,
            |acc: int, x: T| acc + x.ghost_serialize().len(),
        ) <= usize::MAX
    }

    open spec fn ghost_serialize(&self) -> Seq<u8> {
        (self@.len() as usize).ghost_serialize() + self@.fold_left(
            Seq::<u8>::empty(),
            |acc: Seq<u8>, x: T| acc + x.ghost_serialize(),
        )
    }
}

impl<T: Marshalable, U: Marshalable> Marshalable for (T, U) {
    open spec fn is_marshalable(&self) -> bool {
        &&& self.0.is_marshalable()
        &&& self.1.is_marshalable()
        &&& self.0.ghost_serialize().len() + self.1.ghost_serialize().len() <= usize::MAX
    }

    open spec fn ghost_serialize(&self) -> Seq<u8> {
        self.0.ghost_serialize() + self.1.ghost_serialize()
    }
}

macro_rules!
    derive_marshalable_for_struct { { $(#[$attr : meta])* $pub : vis struct $newstruct :
    ident $(< $($poly : ident : Marshalable),+ $(,)? >)? { $($fieldvis : vis $field :
    ident : $fieldty : ty),+ $(,)? } } => { ::builtin_macros::verus! { impl $(< $($poly :
    Marshalable),* >)? Marshalable for $newstruct $(< $($poly),* >)? { open spec fn
    is_marshalable(& self) -> bool { $(&&& self.$field .is_marshalable())* &&& 0 $(+ self
    .$field .ghost_serialize().len())* <= usize::MAX } open spec fn ghost_serialize(&
    self) -> Seq < u8 > { Seq::empty() $(+ self.$field .ghost_serialize())* } } } } }

macro_rules! marshalable_by_bijection { { [$type : ty] <-> [$marshalable : ty];
    forward($self : ident) $forward : expr; backward($m : ident) $backward : expr; } => {
    ::builtin_macros::verus! { impl $type { pub open spec fn
    forward_bijection_for_view_equality_do_not_use_for_anything_else($self : Self) ->
    $marshalable { $forward } } impl Marshalable for $type { open spec fn
    is_marshalable($self : & Self) -> bool { $forward .is_marshalable() } open spec fn
    ghost_serialize($self : & Self) -> Seq < u8 > { $forward .ghost_serialize() } } } } }

#[verifier::opaque]
pub open spec fn ckeyhashmap_max_serialized_size() -> usize {
    0x100000
}

impl Marshalable for CKeyHashMap {
    open spec fn is_marshalable(&self) -> bool {
        self.to_vec().is_marshalable() && spec_sorted_keys(self.to_vec())
            && self.to_vec().ghost_serialize().len() <= (ckeyhashmap_max_serialized_size() as int)
    }

    open spec fn ghost_serialize(&self) -> Seq<u8> {
        self.to_vec().ghost_serialize()
    }
}

pub open spec fn max_val_len() -> int {
    1024
}

pub open spec fn valid_key(key: AbstractKey) -> bool {
    true
}

pub open spec fn valid_value(value: AbstractValue) -> bool {
    value.len() < max_val_len()
}

pub open spec fn max_hashtable_size() -> int {
    62
}

pub open spec fn valid_hashtable(h: Hashtable) -> bool {
    &&& h.dom().len() < max_hashtable_size()
    &&& (forall|k| h.dom().contains(k) ==> valid_key(k) && #[trigger] valid_value(h[k]))
}

pub type CKey = SHTKey;

pub type AbstractKey = SHTKey;

pub type AbstractValue = Seq<u8>;

pub type Hashtable = Map<AbstractKey, AbstractValue>;

marshalable_by_bijection! { [SHTKey] <-> [u64]; forward(self) self
    .ukey; backward(x) SHTKey { ukey : x }; }

derive_marshalable_for_struct! { pub struct
    CKeyKV { pub k : CKey, pub v : Vec::< u8 >, } }

#[allow(non_snake_case)]
pub proof fn lemma_is_marshalable_CKeyHashMap(h: CKeyHashMap)
    requires
        valid_hashtable(h@),
    ensures
        h.is_marshalable(),
{
}

} // verus!
