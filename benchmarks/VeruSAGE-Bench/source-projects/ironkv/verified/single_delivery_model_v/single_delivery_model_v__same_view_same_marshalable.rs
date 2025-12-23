extern crate verus_builtin_macros as builtin_macros;
use vstd::prelude::*;
use std::collections;
use vstd::bytes::*;

fn main() {}

verus!{

// File: cmessage_v.rs
#[allow(inconsistent_fields)]   // Not sure why we need this; v sure looks equivalent to me!
pub enum CMessage {
  GetRequest{ k: CKey},
  SetRequest{ k: CKey, v: Option::<Vec<u8>>},
  Reply{ k: CKey, v: Option::<Vec::<u8>> },
  Redirect{ k: CKey, id: EndPoint },
  Shard{ kr: KeyRange::<CKey>, recipient: EndPoint },
  Delegate{ range: KeyRange::<CKey>, h: CKeyHashMap},
}

pub open spec fn optional_value_view(ov: Option::<Vec::<u8>>) -> Option::<Seq::<u8>>
{
    match ov {
        Some(v) => Some(v@),
        None => None,
    }
}

impl CMessage {

  pub open spec fn view(self) -> Message {
    match self {
        CMessage::GetRequest { k } => Message::GetRequest { key: k },
        CMessage::SetRequest { k, v } => Message::SetRequest { key: k, value: optional_value_view(v) },
        CMessage::Reply { k, v } => Message::Reply { key: k, value: optional_value_view(v) },
        CMessage::Redirect { k, id } => Message::Redirect { key: k, id: id@ },
        CMessage::Shard { kr, recipient } => Message::Shard { range: kr, recipient: recipient@ },
        CMessage::Delegate { range, h } => Message::Delegate { range: range, h: h@ },
    }
  }

}


impl CSingleMessage {

  pub open spec fn view(self) -> SingleMessage<Message> {
    match self {
        CSingleMessage::Message { seqno, dst, m } => SingleMessage::Message { seqno: seqno as nat, dst: dst@, m: m@ },
        CSingleMessage::Ack { ack_seqno } => SingleMessage::Ack { ack_seqno: ack_seqno as nat },
        CSingleMessage::InvalidMessage { } => SingleMessage::InvalidMessage {  },
    }
  }

	#[verifier::external_body]
  pub proof fn view_equal_spec()
    ensures forall |x: &CSingleMessage, y: &CSingleMessage| #[trigger] x.view_equal(y) <==> x@ == y@
	{
		unimplemented!()
	}

}


pub struct CPacket {
  pub dst: EndPoint,
  pub src: EndPoint,
  pub msg: CSingleMessage,
}


// File: marshal_v.rs
pub trait Marshalable : Sized {

  spec fn is_marshalable(&self) -> bool;

	#[verifier::external_body]
  spec fn ghost_serialize(&self) -> Seq<u8>
    recommends self.is_marshalable()
  {unimplemented!()}

  spec fn view_equal(&self, other: &Self) -> bool;

	#[verifier::external_body]
  proof fn lemma_same_views_serialize_the_same(&self, other: &Self)
    requires
      self.view_equal(other),
    ensures
      self.is_marshalable() == other.is_marshalable(),
      self.ghost_serialize() == other.ghost_serialize()
  {unimplemented!()}

}


impl Marshalable for u64 {

  open spec fn view_equal(&self, other: &Self) -> bool {
    self@ === other@
  }

  open spec fn is_marshalable(&self) -> bool {
    true
  }

  open spec fn ghost_serialize(&self) -> Seq<u8> {
    spec_u64_to_le_bytes(*self)
  }

	#[verifier::external_body]
  proof fn lemma_same_views_serialize_the_same(self: &Self, other: &Self)
	{
		unimplemented!()
	}

}


impl Marshalable for usize {

  open spec fn view_equal(&self, other: &Self) -> bool {
    self@ === other@
  }

  open spec fn is_marshalable(&self) -> bool {
    &&& *self as int <= u64::MAX
  }

  open spec fn ghost_serialize(&self) -> Seq<u8> {
    (*self as u64).ghost_serialize()
  }

	#[verifier::external_body]
  proof fn lemma_same_views_serialize_the_same(self: &Self, other: &Self)
	{
		unimplemented!()
	}

}


impl Marshalable for Vec<u8> {

  open spec fn view_equal(&self, other: &Self) -> bool {
    self@ === other@
  }

  open spec fn is_marshalable(&self) -> bool {
    self@.len() <= usize::MAX &&
    (self@.len() as usize).ghost_serialize().len() + self@.len() as int <= usize::MAX
  }

  open spec fn ghost_serialize(&self) -> Seq<u8> {
    (self@.len() as usize).ghost_serialize()
      + self@
  }

	#[verifier::external_body]
  proof fn lemma_same_views_serialize_the_same(self: &Self, other: &Self)
	{
		unimplemented!()
	}

}


impl<T: Marshalable> Marshalable for Option<T> {

  open spec fn view_equal(&self, other: &Self) -> bool {
    match (self, other) {
      (None, None) => true,
      (Some(s), Some(o)) => s.view_equal(o),
      _ => false,
    }
  }

  open spec fn is_marshalable(&self) -> bool {
    match self {
      None => true,
      Some(x) => x.is_marshalable() && 1 + x.ghost_serialize().len() <= usize::MAX,
    }
  }

  open spec fn ghost_serialize(&self) -> Seq<u8>
  // req, ens from trait
  {
    match self {
      None => seq![0],
      Some(x) => seq![1] + x.ghost_serialize(),
    }
  }

	#[verifier::external_body]
  proof fn lemma_same_views_serialize_the_same(self: &Self, other: &Self)
	{
		unimplemented!()
	}

}


impl<T: Marshalable> Marshalable for Vec<T> {

  open spec fn view_equal(&self, other: &Self) -> bool {
    let s = self@;
    let o = other@;
    s.len() == o.len() && (forall |i: int| 0 <= i < s.len() ==> #[trigger] s[i].view_equal(&o[i]))
  }

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

	#[verifier::external_body]
  proof fn lemma_same_views_serialize_the_same(self: &Self, other: &Self)
	{
		unimplemented!()
	}

}


impl<T: Marshalable, U: Marshalable> Marshalable for (T, U) {

  open spec fn view_equal(&self, other: &Self) -> bool {
    self.0.view_equal(&other.0) && self.1.view_equal(&other.1)
  }

  open spec fn is_marshalable(&self) -> bool {
    &&& self.0.is_marshalable()
    &&& self.1.is_marshalable()
    &&& self.0.ghost_serialize().len() + self.1.ghost_serialize().len() <= usize::MAX
  }

  open spec fn ghost_serialize(&self) -> Seq<u8> {
    self.0.ghost_serialize() + self.1.ghost_serialize()
  }

	#[verifier::external_body]
  proof fn lemma_same_views_serialize_the_same(self: &Self, other: &Self)
	{
		unimplemented!()
	}
}

#[allow(unused_macros)]
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

        open spec fn view_equal(&self, other: &Self) -> bool {
          $(
            &&& self.$field.view_equal(&other.$field)
          )*
        }

        open spec fn is_marshalable(&self) -> bool {
          $(
            &&& self.$field.is_marshalable()
          )*
          &&& 0 $(+ self.$field.ghost_serialize().len())* <= usize::MAX
        }

        open spec fn ghost_serialize(&self) -> Seq<u8> {
          Seq::empty() $(+ self.$field.ghost_serialize())*
        }

	#[verifier::external_body]
        proof fn lemma_same_views_serialize_the_same(self: &Self, other: &Self)
	{
		unimplemented!()
	}
      }
    }
  }
}

macro_rules! derive_marshalable_for_enum {
  {
    $( #[$attr:meta] )*
    $pub:vis
    enum $newenum:ident $(< $($poly:ident : Marshalable),+ $(,)? >)? {
      $(
        #[tag = $tag:literal]
        $variant:ident $( { $(#[o=$memother:ident] $member:ident : $memberty:ty),* $(,)? } )?
      ),+
      $(,)?
    }
    $( [rlimit attr = $rlimitattr:meta] )?
  } => {
    ::builtin_macros::verus! {

      impl $(< $($poly : Marshalable),+ >)? Marshalable for $newenum $(< $($poly),+ >)? {

        open spec fn view_equal(&self, other: &Self) -> bool {
          &&& match (self, other) {
            $(
              (
                $newenum::$variant $( { $($member),* } )?,
                $newenum::$variant $( { $($member: $memother),* } )?
              ) => {
                $( $(&&& $member.view_equal($memother))* )?
                &&& true
              }
            ),+
            _ => false,
          }
        }

        open spec fn is_marshalable(&self) -> bool {
          &&& match self {
            $(
              $newenum::$variant $( { $($member),* } )? => {
                $( $(&&& $member.is_marshalable())* )?
                &&& 1 $( $(+ $member.ghost_serialize().len())* )? <= usize::MAX
              }
            ),+
          }
        }

        open spec fn ghost_serialize(&self) -> Seq<u8> {
          match self {
            $(
              $newenum::$variant $( { $($member),* } )? => {
                seq![$tag] $( $(+ $member.ghost_serialize())* )?
              }
            ),*
          }
        }

	#[verifier::external_body]
        proof fn lemma_same_views_serialize_the_same(self: &Self, other: &Self)
	{
		unimplemented!()
	}
      }
    }
  }
}


#[allow(unused_macros)]
macro_rules! define_enum_and_derive_marshalable {
  {
    $( #[$attr:meta] )*
    $pub:vis
    enum $newenum:ident $(< $($poly:ident : Marshalable),+ $(,)? >)? {
      $(
        #[tag = $tag:literal]
        $variant:ident $( { $(#[o=$memother:ident] $member:ident : $memberty:ty),* $(,)? } )?
      ),+
      $(,)?
    }
    $( [rlimit attr = $rlimitattr:meta] )?
  } => {

    // We first re-generate the enum definition itself, so that the enum exists
    ::builtin_macros::verus! {
    $( #[$attr] )*
    $pub
    enum $newenum $(< $($poly : Marshalable),+ >)? {
      $($variant $( { $($member : $memberty),* } )?),+
    }
    }

    // ..and then implement `Marshalable` on it.
    derive_marshalable_for_enum! {
      $( #[$attr] )*
      $pub
      enum $newenum $(< $($poly : Marshalable),+ >)? {
        $(
          #[tag = $tag]
          $variant $( { $(#[o=$memother] $member : $memberty),* } )?
        ),+
      }
      $( [rlimit attr = $rlimitattr] )?
    }
  };
}
#[allow(unused_macros)]
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

                open spec fn view_equal(&self, other: &Self) -> bool {
                    self.forward_bijection_for_view_equality_do_not_use_for_anything_else().view_equal(
                      &other.forward_bijection_for_view_equality_do_not_use_for_anything_else())
                }

                open spec fn is_marshalable($self: &Self) -> bool {
                    $forward.is_marshalable()
                }

                open spec fn ghost_serialize($self: &Self) -> Seq<u8>
                // req, ens from trait
                {
                    $forward.ghost_serialize()
                }

	        #[verifier::external_body]
                proof fn lemma_same_views_serialize_the_same(self: &Self, other: &Self)
	        {
		unimplemented!()
	        }

            }
        }
    }
}


// File: single_delivery_model_v.rs
pub proof fn same_view_same_marshalable(x: &CSingleMessage, y: &CSingleMessage)
requires
    x@ == y@,
ensures
    x.is_marshalable() == y.is_marshalable(),
{
    CSingleMessage::view_equal_spec();
    assert(x.view_equal(y));
    x.lemma_same_views_serialize_the_same(y);
}

pub enum ReceiveImplResult {
    // What does caller need to do?
    FreshPacket{ack: CPacket},      // Buffer the receivedPacket, send an ack
    DuplicatePacket{ack: CPacket},  // Send another ack
    AckOrInvalid,                   // No obligation
}


// File: abstract_end_point_t.rs
pub struct AbstractEndPoint {
    pub id: Seq<u8>,
}


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

}


pub struct CKeyKV {
    pub k: CKey,
    pub v: Vec<u8>,
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


// File: io_t.rs
#[derive(PartialEq, Eq, Hash)]
pub struct EndPoint {
    pub id: Vec<u8>,
}

impl EndPoint {

    pub open spec fn view(self) -> AbstractEndPoint {
        AbstractEndPoint{id: self.id@}
    }

}


// File: keys_t.rs
pub struct KeyIterator<K: KeyTrait + VerusClone> {
    // None means we hit the end
    pub k: Option<K>,
}

pub struct KeyRange<K: KeyTrait + VerusClone> {
    pub lo: KeyIterator<K>,
    pub hi: KeyIterator<K>,
}

#[derive(Eq,PartialEq,Hash)]
pub struct SHTKey {
    pub // workaround
        ukey: u64,
}


// File: message_t.rs
pub enum Message {
    GetRequest {
        key: AbstractKey,
    },
    SetRequest {
        key: AbstractKey,
        value: Option<AbstractValue>,
    },
    Reply {
        key: AbstractKey,
        value: Option<AbstractValue>,
    },
    Redirect {
        key: AbstractKey,
        id: AbstractEndPoint,
    },
    Shard {
        range: KeyRange<AbstractKey>,
        recipient: AbstractEndPoint,
    },
    Delegate {
        range: KeyRange<AbstractKey>,
        h: Hashtable,
    },
}


// File: single_message_t.rs
pub enum SingleMessage<MT> {
    Message {
        seqno: nat,
        dst: AbstractEndPoint,
        m: MT,
    },
    Ack {
        ack_seqno: nat,
    }, // I have received everything up to and including seqno
    InvalidMessage {}, // ... what parse returns for raw messages we can't otherwise parse into a valid message above
}


// File: marshal_ironsht_specific_v.rs
	#[verifier::opaque]
    pub open spec fn ckeyhashmap_max_serialized_size() -> usize {
        0x100000
    }


    impl Marshalable for CKeyHashMap {

        open spec fn view_equal(&self, other: &Self) -> bool {
            self@ === other@
        }

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

	#[verifier::external_body]
        proof fn lemma_same_views_serialize_the_same(self: &Self, other: &Self)
	{
		unimplemented!()
	}

    }


pub trait KeyTrait {}

pub trait VerusClone {}

impl VerusClone for SHTKey {}


impl KeyTrait for SHTKey {}

///////
/* $line_count$Proof$ */ define_enum_and_derive_marshalable! {
/* $line_count$Exec$ */ pub enum CSingleMessage {
/* $line_count$Exec$ */   #[tag = 0]
/* $line_count$Exec$ */   Message{ #[o=o0] seqno: u64, #[o=o1] dst: EndPoint, #[o=o2] m: CMessage },
/* $line_count$Exec$ */   #[tag = 1]
/* $line_count$Exec$ */   // I got everything up to and including `ack_seqno`
/* $line_count$Exec$ */   Ack{ #[o=o0] ack_seqno: u64},
/* $line_count$Exec$ */   #[tag = 2]
/* $line_count$Exec$ */   InvalidMessage,
/* $line_count$Exec$ */ }
/* $line_count$Proof$ */ [rlimit attr = verifier::rlimit(25)]
}

pub type AbstractKey = SHTKey;
pub type CKey = SHTKey;
pub type Hashtable = Map<AbstractKey, AbstractValue>;
pub type AbstractValue = Seq<u8>;
type ID = EndPoint;

    /* $line_count$Proof$ */ derive_marshalable_for_enum! {
    /* $line_count$Proof$ */     pub enum CMessage {
    /* $line_count$Proof$ */         #[tag = 0]
    /* $line_count$Proof$ */         GetRequest{ #[o=o0] k: CKey},
    /* $line_count$Proof$ */         #[tag = 1]
    /* $line_count$Proof$ */         SetRequest{ #[o=o0] k: CKey, #[o=o1] v: Option::<Vec<u8>>},
    /* $line_count$Proof$ */         #[tag = 2]
    /* $line_count$Proof$ */         Reply{ #[o=o0] k: CKey, #[o=o1] v: Option::<Vec::<u8>> },
    /* $line_count$Proof$ */         #[tag = 3]
    /* $line_count$Proof$ */         Redirect{ #[o=o0] k: CKey, #[o=o1] id: EndPoint },
    /* $line_count$Proof$ */         #[tag = 4]
    /* $line_count$Proof$ */         Shard{ #[o=o0] kr: KeyRange::<CKey>, #[o=o1] recipient: EndPoint },
    /* $line_count$Proof$ */         #[tag = 5]
    /* $line_count$Proof$ */         Delegate{ #[o=o0] range: KeyRange::<CKey>, #[o=o1] h: CKeyHashMap},
    /* $line_count$Proof$ */     }
    /* $line_count$Proof$ */     [rlimit attr = verifier::rlimit(20)]
    /* $line_count$Proof$ */ }


    /* $line_count$Proof$ */ marshalable_by_bijection! {
    /* $line_count$Proof$ */     [KeyRange::<CKey>] <-> [(Option::<u64>, Option::<u64>)];
    /* $line_count$Proof$ */     forward(self) {
    /* $line_count$Proof$ */         (
    /* $line_count$Proof$ */             match &self.lo.k {
    /* $line_count$Proof$ */                 None => None,
    /* $line_count$Proof$ */                 Some(x) => Some(x.ukey),
    /* $line_count$Proof$ */             },
    /* $line_count$Proof$ */             match &self.hi.k {
    /* $line_count$Proof$ */                 None => None,
    /* $line_count$Proof$ */                 Some(x) => Some(x.ukey),
    /* $line_count$Proof$ */             },
    /* $line_count$Proof$ */         )
    /* $line_count$Proof$ */     };
    /* $line_count$Proof$ */     backward(x) {
    /* $line_count$Proof$ */         KeyRange {
    /* $line_count$Proof$ */             lo: KeyIterator {
    /* $line_count$Proof$ */                 k: match x.0 {
    /* $line_count$Proof$ */                     None => None,
    /* $line_count$Proof$ */                     Some(x) => Some(SHTKey { ukey: x }),
    /* $line_count$Proof$ */                 }
    /* $line_count$Proof$ */             },
    /* $line_count$Proof$ */             hi: KeyIterator {
    /* $line_count$Proof$ */                 k: match x.1 {
    /* $line_count$Proof$ */                     None => None,
    /* $line_count$Proof$ */                     Some(x) => Some(SHTKey { ukey: x }),
    /* $line_count$Proof$ */                 }
    /* $line_count$Proof$ */             },
    /* $line_count$Proof$ */         }
    /* $line_count$Proof$ */     };
    /* $line_count$Proof$ */ }

    /* $line_count$Proof$}$ */ marshalable_by_bijection! {
    /* $line_count$Proof$}$ */    [EndPoint] <-> [Vec::<u8>];
    /* $line_count$Proof$}$ */    forward(self) self.id;
    /* $line_count$Proof$}$ */    backward(x) EndPoint { id: x };
    /* $line_count$Proof$}$ */ }


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
