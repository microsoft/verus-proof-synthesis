use vstd::prelude::*;
use std::collections;

fn main() {}

verus! {

pub trait VerusClone : Sized {
    fn clone(&self) -> (o: Self)
        ensures o == self;  // this is way too restrictive; it kind of demands Copy. But we don't have a View trait yet. :v(
}

// #[derive(Copy, Clone)]
#[derive(PartialEq, Eq, Hash)]
pub struct EndPoint {
    pub id: Vec<u8>,
}

impl EndPoint {

    pub open spec fn view(self) -> AbstractEndPoint {
        AbstractEndPoint{id: self.id@}
    }

}

pub struct AbstractEndPoint {
    pub id: Seq<u8>,
}

#[verifier(external_body)]
pub struct CKeyHashMap {
  m: collections::HashMap<CKey, Vec<u8>>,
}

impl CKeyHashMap{
    pub uninterp spec fn view(self) -> Map<AbstractKey, Seq<u8>>;
}

#[derive(Eq,PartialEq,Hash)]
pub struct SHTKey {
    pub // workaround
        ukey: u64,
}
impl SHTKey {
    pub fn clone(&self) -> (out: SHTKey)
    ensures out == self
    {
        SHTKey{ ukey: self.ukey }
    }
}
impl KeyTrait for SHTKey {}
impl VerusClone for SHTKey {
    fn clone(&self) -> (o: Self)
        //ensures o == self
    {
        SHTKey{ukey: self.ukey}
    }
}

pub type CKey = SHTKey;
pub type AbstractKey = SHTKey;
pub type AbstractValue = Seq<u8>;
pub type Hashtable = Map<AbstractKey, AbstractValue>;

pub trait KeyTrait : Sized {}

pub struct KeyRange<K: KeyTrait + VerusClone>{
    pub lo: KeyIterator<K>,
    pub hi: KeyIterator<K>,
}

pub struct KeyIterator<K: KeyTrait + VerusClone>{
    // None means we hit the end
    pub k: Option<K>,
}

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

  pub open spec fn view_equal(&self, other: &Self) -> bool {
            self@ === other@
  }

  pub proof fn view_equal_spec()
    ensures forall |x: &CMessage, y: &CMessage| #[trigger] x.view_equal(y) <==> x@ == y@
  {
    assert forall |x: &CMessage, y: &CMessage|
      #[trigger] x.view_equal(y) <==> x@ == y@ by
    {
      match (x, y) {
        (CMessage::GetRequest { k: k1 }, CMessage::GetRequest { k: k2 }) => {},
        (CMessage::SetRequest { k: k1, v: v1 }, CMessage::SetRequest { k: k2, v: v2 }) => {},
        (CMessage::Reply { k: k1, v: v1 }, CMessage::Reply { k: k2, v: v2 }) => {},
        (CMessage::Redirect { k: k1, id: id1 }, CMessage::Redirect { k: k2, id: id2 }) => {},
        (CMessage::Shard { kr: kr1, recipient: r1 }, CMessage::Shard { kr: kr2, recipient: r2 }) => {},
        (CMessage::Delegate { range: r1, h: h1 }, CMessage::Delegate { range: r2, h: h2 }) => {},
        _ => {
          assert(!x.view_equal(y) && x@ != y@);
        }
      }
    }
  }

}
}
