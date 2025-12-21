use std::collections;
use vstd::prelude::*;
fn main() {}
verus! {

#[derive(PartialEq, Eq, Hash)]
pub struct EndPoint {
    pub id: Vec<u8>,
}

impl EndPoint {
    pub open spec fn view(self) -> AbstractEndPoint {
        AbstractEndPoint { id: self.id@ }
    }
}

pub struct AbstractEndPoint {
    pub id: Seq<u8>,
}

#[verifier(external_body)]
pub struct CKeyHashMap {
    m: collections::HashMap<CKey, Vec<u8>>,
}

impl CKeyHashMap {
    pub uninterp spec fn view(self) -> Map<AbstractKey, Seq<u8>>;
}

#[derive(Eq, PartialEq, Hash)]
pub struct SHTKey {
    pub ukey: u64,
}

pub type CKey = SHTKey;

pub type AbstractKey = SHTKey;

pub type AbstractValue = Seq<u8>;

pub type Hashtable = Map<AbstractKey, AbstractValue>;

pub trait KeyTrait: Sized {

}

pub trait VerusClone: Sized {
    fn clone(&self) -> (o: Self)
        ensures
            o == self,
    ;
}

pub struct KeyRange<K: KeyTrait + VerusClone> {
    pub lo: KeyIterator<K>,
    pub hi: KeyIterator<K>,
}

pub struct KeyIterator<K: KeyTrait + VerusClone> {
    pub k: Option<K>,
}

impl<K: VerusClone + KeyTrait> VerusClone for KeyIterator<K> {
    fn clone(&self) -> Self {
        KeyIterator {
            k: match &self.k {
                Some(v) => Some(v.clone()),
                None => None,
            },
        }
    }
}

impl<K: VerusClone + KeyTrait> VerusClone for KeyRange<K> {
    fn clone(&self) -> Self {
        KeyRange { lo: self.lo.clone(), hi: self.hi.clone() }
    }
}

impl KeyTrait for SHTKey {

}

impl VerusClone for SHTKey {
    fn clone(&self) -> (o: Self) {
        SHTKey { ukey: self.ukey }
    }
}

pub enum Message {
    GetRequest { key: AbstractKey },
    SetRequest { key: AbstractKey, value: Option<AbstractValue> },
    Reply { key: AbstractKey, value: Option<AbstractValue> },
    Redirect { key: AbstractKey, id: AbstractEndPoint },
    Shard { range: KeyRange<AbstractKey>, recipient: AbstractEndPoint },
    Delegate { range: KeyRange<AbstractKey>, h: Hashtable },
}

#[allow(inconsistent_fields)]
pub enum CMessage {
    GetRequest { k: CKey },
    SetRequest { k: CKey, v: Option::<Vec<u8>> },
    Reply { k: CKey, v: Option::<Vec::<u8>> },
    Redirect { k: CKey, id: EndPoint },
    Shard { kr: KeyRange::<CKey>, recipient: EndPoint },
    Delegate { range: KeyRange::<CKey>, h: CKeyHashMap },
}

pub open spec fn optional_value_view(ov: Option::<Vec::<u8>>) -> Option::<Seq::<u8>> {
    match ov {
        Some(v) => Some(v@),
        None => None,
    }
}

impl CMessage {
    pub open spec fn view(self) -> Message {
        match self {
            CMessage::GetRequest { k } => Message::GetRequest { key: k },
            CMessage::SetRequest { k, v } => Message::SetRequest {
                key: k,
                value: optional_value_view(v),
            },
            CMessage::Reply { k, v } => Message::Reply { key: k, value: optional_value_view(v) },
            CMessage::Redirect { k, id } => Message::Redirect { key: k, id: id@ },
            CMessage::Shard { kr, recipient } => Message::Shard {
                range: kr,
                recipient: recipient@,
            },
            CMessage::Delegate { range, h } => Message::Delegate { range: range, h: h@ },
        }
    }
}

pub enum SingleMessage<MT> {
    Message { seqno: nat, dst: AbstractEndPoint, m: MT },
    Ack { ack_seqno: nat },
    InvalidMessage {  },
}

pub open spec fn abstractify_cmessage_seq(messages: Seq<CSingleMessage>) -> Seq<
    SingleMessage<Message>,
> {
    messages.map_values(|msg: CSingleMessage| msg@)
}

pub enum CSingleMessage {
    Message { seqno: u64, dst: EndPoint, m: CMessage },
    Ack { ack_seqno: u64 },
    InvalidMessage,
}

impl CSingleMessage {
    pub open spec fn view(self) -> SingleMessage<Message> {
        match self {
            CSingleMessage::Message { seqno, dst, m } => SingleMessage::Message {
                seqno: seqno as nat,
                dst: dst@,
                m: m@,
            },
            CSingleMessage::Ack { ack_seqno } => SingleMessage::Ack { ack_seqno: ack_seqno as nat },
            CSingleMessage::InvalidMessage {  } => SingleMessage::InvalidMessage {  },
        }
    }

    #[verifier::external_body]
    pub fn clone_up_to_view(&self) -> (c: Self)
        ensures
            c@ == self@,
    {
        unimplemented!()
    }
}

pub type AckList<MT> = Seq<SingleMessage<MT>>;

pub struct AckState<MT> {
    pub num_packets_acked: nat,
    pub un_acked: AckList<MT>,
}

impl AckState<Message> {
    pub open spec fn new() -> Self {
        AckState { num_packets_acked: 0, un_acked: seq![] }
    }
}

#[verifier::ext_equal]
pub struct CAckState {
    pub num_packets_acked: u64,
    pub un_acked: Vec<CSingleMessage>,
}

impl CAckState {
    pub open spec fn view(&self) -> AckState<Message> {
        AckState {
            num_packets_acked: self.num_packets_acked as nat,
            un_acked: abstractify_cmessage_seq(self.un_acked@),
        }
    }

    pub fn clone_up_to_view(&self) -> (o: Self)
        ensures
            o@ == self@,
    {
        let mut un_acked: Vec<CSingleMessage> = Vec::new();
        let mut i = 0;
        while i < self.un_acked.len() {
            un_acked.push(self.un_acked[i].clone_up_to_view());
            i = i + 1;
        }
        let o = CAckState { num_packets_acked: self.num_packets_acked, un_acked };
        o
    }
}

impl SHTKey {
    pub fn clone(&self) -> (out: SHTKey)
        ensures
            out == self,
    {
        SHTKey { ukey: self.ukey }
    }
}

} // verus!
