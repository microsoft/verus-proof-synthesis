use std::collections;
use vstd::prelude::*;
fn main() {}
verus! {

pub type Hashtable = Map<AbstractKey, AbstractValue>;

#[derive(Eq, PartialEq,
    Hash)]
pub struct SHTKey {
    pub ukey: u64,
}

pub type AbstractKey = SHTKey;

pub type AbstractValue = Seq<u8>;

pub type CKey = SHTKey;

#[verifier(external_body)]
pub struct CKeyHashMap {
    m: collections::HashMap<CKey, Vec<u8>>,
}

impl CKeyHashMap {
    pub uninterp spec fn view(self) -> Map<AbstractKey, Seq<u8>>;
}

pub enum Message {
    GetRequest { key: AbstractKey },
    SetRequest { key: AbstractKey, value: Option<AbstractValue> },
    Reply { key: AbstractKey, value: Option<AbstractValue> },
    Redirect { key: AbstractKey, id: AbstractEndPoint },
    Shard { range: KeyRange<AbstractKey>, recipient: AbstractEndPoint },
    Delegate { range: KeyRange<AbstractKey>, h: Hashtable },
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

pub trait KeyTrait: Sized {

}

pub trait VerusClone: Sized {
    fn clone(&self) -> (o: Self)
        ensures
            o == self,
    ;
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

impl AbstractEndPoint {
    pub open spec fn valid_physical_address(self) -> bool {
        self.id.len() < 0x100000
    }

    pub open spec fn abstractable(self) -> bool {
        self.valid_physical_address()
    }
}

#[verifier(external_body)]
#[verifier::accept_recursive_types(V)]
pub struct HashMap<V> {
    m: collections::HashMap<EndPoint, V>,
}

impl<V> HashMap<V> {
    pub uninterp spec fn view(self) -> Map<AbstractEndPoint, V>;

    #[verifier::external_body]
    pub fn insert(&mut self, key: &EndPoint, value: V)
        ensures
            self@ == old(self)@.insert(key@, value),
    {
        unimplemented!()
    }

    #[verifier(external_body)]
    pub fn new() -> (out: Self)
        ensures
            out@ == Map::<AbstractEndPoint, V>::empty(),
    {
        HashMap { m: collections::HashMap::new() }
    }
}

pub type TombstoneTable = Map<AbstractEndPoint, nat>;

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

#[doc =
    " translates `AckState<MT = CMessage>` (that is, we specialize the message type)"]
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
}

pub struct CTombstoneTable {
    pub epmap: HashMap<u64>,
}

impl CTombstoneTable {
    #[doc =
    " Since I'm a map, I already have a simple view(), hence the special name."]
    pub open spec fn view(&self) -> TombstoneTable {
        self.epmap@.map_values(|v: u64| v as nat)
    }
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

pub open spec fn optional_value_view(ov: Option::<Vec::<u8>>) -> Option::<Seq::<u8>> {
    match ov {
        Some(v) => Some(v@),
        None => None,
    }
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
}

pub struct CSendState {
    pub epmap: HashMap<CAckState>,
}

impl CSendState {
    pub open spec fn view(&self) -> SendState<Message> {
        self.epmap@.map_values(|v: CAckState| v@)
    }
}

pub type SendState<MT> = Map<AbstractEndPoint, AckState<MT>>;

#[verifier::ext_equal]
pub struct SingleDelivery<MT> {
    pub receive_state: TombstoneTable,
    pub send_state: SendState<MT>,
}

impl<MT> SingleDelivery<MT> {
    pub open spec fn init() -> Self {
        SingleDelivery { receive_state: Map::empty(), send_state: Map::empty() }
    }
}

#[doc = " Translates CSingleDeliveryAcct"]
pub struct CSingleDelivery {
    pub receive_state: CTombstoneTable,
    pub send_state: CSendState,
}

impl CSingleDelivery {
    pub open spec fn view(self) -> SingleDelivery<Message> {
        SingleDelivery { receive_state: self.receive_state@, send_state: self.send_state@ }
    }

    pub fn empty() -> (out: Self)
        ensures
            out@ == SingleDelivery::<Message>::init(),
    {
        let result = CSingleDelivery {
            receive_state: CTombstoneTable { epmap: HashMap::new() },
            send_state: CSendState { epmap: HashMap::new() },
        };
        result
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
