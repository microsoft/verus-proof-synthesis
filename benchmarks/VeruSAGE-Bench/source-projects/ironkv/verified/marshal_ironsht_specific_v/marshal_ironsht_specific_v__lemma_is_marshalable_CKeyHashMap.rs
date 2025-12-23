extern crate verus_builtin_macros as builtin_macros;
use vstd::prelude::*;
use std::collections;
use vstd::bytes::*;
use vstd::seq_lib::*;
use vstd::set_lib::*;

fn main() {}

verus!{

// File: hashmap_t.rs
#[verifier(external_body)]
pub struct CKeyHashMap {
  m: collections::HashMap<CKey, Vec<u8>>,
}

impl CKeyHashMap {

    pub uninterp spec fn view(self) -> Map<AbstractKey, Seq<u8>>;

    pub uninterp spec fn spec_to_vec(&self) -> Vec<CKeyKV>;
    #[verifier(external_body)]
    #[verifier(when_used_as_spec(spec_to_vec))]
    pub fn to_vec(&self) -> (res: Vec<CKeyKV>)
    {unimplemented!()}

    pub uninterp spec fn spec_from_vec(v: Vec<CKeyKV>) -> Self;

	#[verifier::external_body]
    pub proof fn lemma_to_vec(self)
      ensures
        #![trigger self.spec_to_vec()]
        Self::spec_from_vec(self.spec_to_vec()) == self,
        self.spec_to_vec().len() == self@.dom().len(),
        spec_sorted_keys(self.spec_to_vec()),
        (forall |i: int|
         #![trigger(self.spec_to_vec()[i])]
         0 <= i < self.spec_to_vec().len() ==> {
             let (k, v) = self.spec_to_vec()[i]@;
             self@.contains_pair(k, v)
        }),
	{
		unimplemented!()
	}

}


pub struct CKeyKV {
    pub k: CKey,
    pub v: Vec<u8>,
}

impl CKeyKV {

    pub open spec fn view(self) -> (AbstractKey, Seq<u8>)
    {
        (self.k, self.v@)
    }

}


pub open spec fn ckeykvlt(a: CKeyKV, b: CKeyKV) -> bool {
    a.k.ukey < b.k.ukey
}

pub open spec fn spec_sorted_keys(v: Vec<CKeyKV>) -> bool {
    // ckeykvlt ensures that this forall does not create a trigger loop on
    // v@[i].k.ukey, v@[i+1].k.ukey, ...
    //
    // we weren't able to fix this by making the whole < the trigger
    forall |i: int, j: int| 0 <= i && i + 1 < v.len() && j == i+1 ==> #[trigger] ckeykvlt(v@[i], v@[j])
}


// File: keys_t.rs
#[derive(Eq,PartialEq,Hash)]
pub struct SHTKey {
    pub // workaround
        ukey: u64,
}


// File: verus_extra/seq_lib_v.rs
	#[verifier::external_body]
pub proof fn lemma_seq_fold_left_append_len_int<A, B>(s: Seq<A>, prefix: Seq<B>, f: spec_fn(A) -> Seq<B>)
  ensures
    s.fold_left(prefix, |sb: Seq<B>, a: A| sb + f(a)).len() as int
    ==
    s.fold_left(prefix.len() as int, |i: int, a: A| i + f(a).len() as int),
  decreases s.len(),
	{
		unimplemented!()
	}

	#[verifier::external_body]
pub proof fn lemma_seq_fold_left_sum_le<A>(s: Seq<A>, init: int, high: int, f: spec_fn(A) -> int)
  requires
    forall |i:int| 0 <= i < s.len() ==> f(s[i]) <= high,
  ensures
    s.fold_left(init, |acc: int, x: A| acc + f(x)) <= init + s.len() * high,
  decreases s.len(),
	{
		unimplemented!()
	}


// File: marshal_v.rs
pub trait Marshalable : Sized {

  spec fn is_marshalable(&self) -> bool;

	#[verifier::external_body]
  spec fn ghost_serialize(&self) -> Seq<u8>
    recommends self.is_marshalable()
  {unimplemented!()}

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
    self@.len() <= usize::MAX &&
    (self@.len() as usize).ghost_serialize().len() + self@.len() as int <= usize::MAX
  }

  open spec fn ghost_serialize(&self) -> Seq<u8> {
    (self@.len() as usize).ghost_serialize()
      + self@
  }

}


impl<T: Marshalable> Marshalable for Vec<T> {

  open spec fn is_marshalable(&self) -> bool {
    &&& self@.len() <= usize::MAX
    &&& (forall |x: T| self@.contains(x) ==> #[trigger] x.is_marshalable())
    &&& (self@.len() as usize).ghost_serialize().len() +
        self@.fold_left(0, |acc: int, x: T| acc + x.ghost_serialize().len()) <= usize::MAX
  }

  open spec fn ghost_serialize(&self) -> Seq<u8> {
    (self@.len() as usize).ghost_serialize()
      + self@.fold_left(Seq::<u8>::empty(), |acc: Seq<u8>, x: T| acc + x.ghost_serialize())
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


macro_rules! derive_marshalable_for_struct {
  {
    $( #[$attr:meta] )*
    $pub:vis
    struct $newstruct:ident $(< $($poly:ident : Marshalable),+ $(,)? >)? {
      $(
        $fieldvis:vis $field:ident : $fieldty:ty
      ),+
      $(,)?
    }
  } => {
    ::builtin_macros::verus! {
      impl $(< $($poly: Marshalable),* >)? Marshalable for $newstruct $(< $($poly),* >)? {

        open spec fn is_marshalable(&self) -> bool {
          $(
            &&& self.$field.is_marshalable()
          )*
          &&& 0 $(+ self.$field.ghost_serialize().len())* <= usize::MAX
        }

        open spec fn ghost_serialize(&self) -> Seq<u8> {
          Seq::empty() $(+ self.$field.ghost_serialize())*
        }

}}}}


macro_rules! marshalable_by_bijection {
    {
        [$type:ty] <-> [$marshalable:ty];
        forward ($self:ident) $forward:expr;
        backward ($m:ident) $backward:expr;
    }
    =>
    {
        ::builtin_macros::verus! {
            impl $type {
                 pub open spec fn forward_bijection_for_view_equality_do_not_use_for_anything_else($self: Self) -> $marshalable {
                  $forward
                }
            }
            impl Marshalable for $type {

                open spec fn is_marshalable($self: &Self) -> bool {
                    $forward.is_marshalable()
                }

                open spec fn ghost_serialize($self: &Self) -> Seq<u8>
                // req, ens from trait
                {
                    $forward.ghost_serialize()
                }

}}}}



// File: marshal_ironsht_specific_v.rs
    #[verifier::opaque]
    pub open spec fn ckeyhashmap_max_serialized_size() -> usize {
        0x100000
    }

    impl Marshalable for CKeyHashMap {

        open spec fn is_marshalable(&self) -> bool {
            self.to_vec().is_marshalable()
                && spec_sorted_keys(self.to_vec())
                && self.to_vec().ghost_serialize().len() <= (ckeyhashmap_max_serialized_size() as int)
        }

        open spec fn ghost_serialize(&self) -> Seq<u8>
        // req, ens from trait
        {
            self.to_vec().ghost_serialize()
        }

}


    #[allow(non_snake_case)]
    pub proof fn lemma_is_marshalable_CKeyHashMap(h: CKeyHashMap)
      requires
        valid_hashtable(h@)
      ensures
        h.is_marshalable()
    {
        lemma_auto_spec_u64_to_from_le_bytes();

        assert(h@.dom().len() < 62);
        h.lemma_to_vec();

        let vec = h.spec_to_vec();

        assert(vec.len() < 62);

        let max_len : int = 10_000;

        assert forall |i:int| 0 <= i < vec.len() implies (
            #[trigger] vec[i].is_marshalable() && vec[i].ghost_serialize().len() < max_len
        ) by {
            let (k, v) = vec[i]@;
            assert(h@.contains_pair(k, v));
            assert(h@.dom().contains(k));
            assert(valid_key(k));
            assert(valid_value(h@[k]));
            assert(vec[i].is_marshalable());
            assert(vec[i].ghost_serialize().len() < max_len);
        }

        reveal(ckeyhashmap_max_serialized_size);

        assert(
            (vec@.len() as usize).ghost_serialize().len() +
                vec@.fold_left(0, |acc: int, x: CKeyKV| acc + x.ghost_serialize().len()) <= 0x100000
        ) by {
            let f = |x: CKeyKV| x.ghost_serialize().len() as int;
            let ag = |acc: int, x: CKeyKV| acc + x.ghost_serialize().len();
            let af = |acc: int, x: CKeyKV| acc + f(x);
            assert forall |i:int| 0 <= i < vec@.len() implies f(vec@[i]) <= max_len by {
                let (k, v) = vec[i]@;
                assert(h@.contains_pair(k, v));
                assert(h@.dom().contains(k));
                assert(valid_key(k));
                assert(valid_value(h@[k]));
                assert(vec[i].is_marshalable());
                assert(vec[i].ghost_serialize().len() < max_len);
            }
            lemma_seq_fold_left_sum_le(vec@, 0, max_len, f);
            assert(ag =~= af);
        }

        assert(
            (vec@.len() as usize).ghost_serialize().len()
                + vec@.fold_left(Seq::<u8>::empty(), |acc: Seq<u8>, x: CKeyKV| acc + x.ghost_serialize()).len()
                <= 0x100000
        ) by {
            let emp = Seq::<u8>::empty();
            let s = |x: CKeyKV| x.ghost_serialize();
            let agl = |acc: int, x: CKeyKV| acc + x.ghost_serialize().len() as int;
            let asl = |acc: int, x: CKeyKV| acc + s(x).len() as int;
            let sg = |acc: Seq<u8>, x: CKeyKV| acc + x.ghost_serialize();
            let sa = |acc: Seq<u8>, x: CKeyKV| acc + s(x);
            lemma_seq_fold_left_append_len_int(vec@, emp, s);
            assert(vec@.fold_left(emp, sa).len() as int == vec@.fold_left(0, asl));
            assert(sa =~= sg);
            assert(vec@.fold_left(emp, sg).len() as int == vec@.fold_left(0, asl));
            assert(agl =~= asl);
            assert(vec@.fold_left(emp, sg).len() == vec@.fold_left(0, agl));
        }

        assert(vec.is_marshalable()) by {
            assert(vec@.len() <= usize::MAX);
            assert(forall |x: CKeyKV| vec@.contains(x) ==> #[trigger] x.is_marshalable());
        }
        assert(spec_sorted_keys(vec));

        assert(h.is_marshalable());
    }


// File: app_interface_t.rs
pub open spec fn max_val_len() -> int { 1024 }

pub open spec fn valid_key(key: AbstractKey) -> bool { true }

pub open spec fn valid_value(value: AbstractValue) -> bool { value.len() < max_val_len() }


// File: host_protocol_t.rs
pub open spec fn max_hashtable_size() -> int
{
    62
}

pub open spec fn valid_hashtable(h: Hashtable) -> bool
{
    &&& h.dom().len() < max_hashtable_size()
    &&& (forall |k| h.dom().contains(k) ==> valid_key(k) && #[trigger] valid_value(h[k]))
}

////////////
pub type CKey=SHTKey;
pub type AbstractKey=SHTKey;
pub type AbstractValue = Seq<u8>;
pub type Hashtable = Map<AbstractKey, AbstractValue>;
    /* $line_count$Proof$ */ marshalable_by_bijection! {
    /* $line_count$Proof$ */     [SHTKey] <-> [u64];
    /* $line_count$Proof$ */     forward(self) self.ukey;
    /* $line_count$Proof$ */     backward(x) SHTKey { ukey: x };
    /* $line_count$Proof$ */ }


    /* $line_count$Proof$ */ derive_marshalable_for_struct! {
    /* $line_count$Proof$ */     pub struct CKeyKV {
    /* $line_count$Proof$ */         pub k: CKey,
    /* $line_count$Proof$ */         pub v: Vec::<u8>,
    /* $line_count$Proof$ */     }
    /* $line_count$Proof$ */ }



}
