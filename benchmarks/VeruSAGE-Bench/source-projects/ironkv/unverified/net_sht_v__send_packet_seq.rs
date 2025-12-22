extern crate verus_builtin_macros as builtin_macros;
use std::collections;
use std::time::SystemTime;
use vstd::bytes::*;
use vstd::prelude::*;
fn main() {}
verus! {

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
    pub open spec fn abstractable(self) -> bool {
        match self {
            CMessage::Redirect { k, id } => id@.abstractable(),
            CMessage::Shard { kr, recipient } => recipient@.abstractable(),
            _ => true,
        }
    }

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

impl CSingleMessage {
    pub open spec fn abstractable(self) -> bool {
        match self {
            CSingleMessage::Message { seqno: _, dst, m } => dst@.abstractable() && m.abstractable(),
            CSingleMessage::Ack { ack_seqno: _ } => true,
            CSingleMessage::InvalidMessage {  } => true,
        }
    }

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

pub struct CPacket {
    pub dst: EndPoint,
    pub src: EndPoint,
    pub msg: CSingleMessage,
}

impl CPacket {
    pub open spec fn view(self) -> Packet {
        Packet { dst: self.dst@, src: self.src@, msg: self.msg@ }
    }

    pub open spec fn abstractable(self) -> bool {
        &&& self.dst.abstractable()
        &&& self.src.abstractable()
        &&& self.msg.abstractable()
    }
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

impl<T: Marshalable> Marshalable for Option<T> {
    open spec fn is_marshalable(&self) -> bool {
        match self {
            None => true,
            Some(x) => x.is_marshalable() && 1 + x.ghost_serialize().len() <= usize::MAX,
        }
    }

    open spec fn ghost_serialize(&self) -> Seq<u8> {
        match self {
            None => seq![0],
            Some(x) => seq![1] + x.ghost_serialize(),
        }
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

macro_rules! derive_marshalable_for_enum { { $(#[$attr : meta])* $pub : vis enum
    $newenum : ident $(< $($poly : ident : Marshalable),+ $(,)? >)? { $(#[tag = $tag :
    literal] $variant : ident $({ $(#[o =$memother : ident] $member : ident : $memberty :
    ty),* $(,)? })?),+ $(,)? } $([rlimit attr = $rlimitattr : meta])? } => {
    ::builtin_macros::verus! { impl $(< $($poly : Marshalable),+ >)? Marshalable for
    $newenum $(< $($poly),+ >)? { open spec fn is_marshalable(& self) -> bool { &&& match
    self { $($newenum ::$variant $({ $($member),* })? => { $($(&&& $member
    .is_marshalable())*)? &&& 1 $($(+ $member .ghost_serialize().len())*)? <= usize::MAX
    }),+ } } open spec fn ghost_serialize(& self) -> Seq < u8 > { match self { $($newenum
    ::$variant $({ $($member),* })? => { seq![$tag] $($(+ $member .ghost_serialize())*)?
    }),* } } } } } }

#[allow(unused_macros)] macro_rules!
    define_enum_and_derive_marshalable { { $(#[$attr : meta])* $pub : vis enum $newenum :
    ident $(< $($poly : ident : Marshalable),+ $(,)? >)? { $(#[tag = $tag : literal]
    $variant : ident $({ $(#[o =$memother : ident] $member : ident : $memberty : ty),*
    $(,)? })?),+ $(,)? } $([rlimit attr = $rlimitattr : meta])? } => {
    ::builtin_macros::verus! { $(#[$attr])* $pub enum $newenum $(< $($poly :
    Marshalable),+ >)? { $($variant $({ $($member : $memberty),* })?),+ } }
    derive_marshalable_for_enum! { $(#[$attr])* $pub enum $newenum $(< $($poly :
    Marshalable),+ >)? { $(#[tag = $tag] $variant $({ $(#[o =$memother] $member :
    $memberty),* })?),+ } $([rlimit attr = $rlimitattr])? } }; }

macro_rules!
    marshalable_by_bijection { { [$type : ty] <-> [$marshalable : ty]; forward($self :
    ident) $forward : expr; backward($m : ident) $backward : expr; } => {
    ::builtin_macros::verus! { impl $type { pub open spec fn
    forward_bijection_for_view_equality_do_not_use_for_anything_else($self : Self) ->
    $marshalable { $forward } } impl Marshalable for $type { open spec fn
    is_marshalable($self : & Self) -> bool { $forward .is_marshalable() } open spec fn
    ghost_serialize($self : & Self) -> Seq < u8 > { $forward .ghost_serialize() } } } } }

pub enum ReceiveResult {
    Fail,
    Timeout,
    Packet { cpacket: CPacket },
}

pub open spec fn net_packet_is_abstractable(net: NetPacket) -> bool {
    true
}

pub open spec fn sht_demarshal_data(data: Seq<u8>) -> CSingleMessage
    recommends
        exists|v: CSingleMessage| v.is_marshalable() && v.ghost_serialize() == data,
{
    let v = choose|v: CSingleMessage| v.is_marshalable() && v.ghost_serialize() == data;
    v
}

pub open spec fn abstractify_net_packet_to_lsht_packet(net: NetPacket) -> LSHTPacket
    recommends
        net_packet_is_abstractable(net),
{
    LPacket { dst: net.dst, src: net.src, msg: (sht_demarshal_data(net.msg))@ }
}

pub open spec fn abstractify_net_packet_to_sht_packet(net: NetPacket) -> Packet
    recommends
        net_packet_is_abstractable(net),
{
    let lp = abstractify_net_packet_to_lsht_packet(net);
    Packet { dst: lp.dst, src: lp.src, msg: lp.msg }
}

pub open spec fn outbound_packet_is_valid(cpacket: &CPacket) -> bool {
    &&& cpacket.abstractable()
    &&& cpacket.msg.is_marshalable()
    &&& !(cpacket.msg is InvalidMessage)
}

pub open spec fn send_log_entry_reflects_packet(event: NetEvent, cpacket: &CPacket) -> bool {
    &&& event is Send
    &&& true
    &&& cpacket.abstractable()
    &&& cpacket@ == abstractify_net_packet_to_sht_packet(event.arrow_Send_s())
}

#[verifier::external_body]
pub fn send_packet(cpacket: &CPacket, netc: &mut NetClient) -> (rc: (bool, Ghost<Option<NetEvent>>))
    requires
        old(netc).ok(),
        outbound_packet_is_valid(cpacket),
        cpacket.src@ == old(netc).my_end_point(),
    ensures
        netc.my_end_point() == old(netc).my_end_point(),
        ({
            let (ok, Ghost(net_event)) = rc;
            {
                &&& netc.ok() <==> ok
                &&& ok ==> net_event is Some
                &&& ok ==> netc.history() == old(netc).history() + seq![net_event.unwrap()]
                &&& ok ==> rc.1@ is Some && send_log_entry_reflects_packet(
                    net_event.unwrap(),
                    &cpacket,
                ) && is_marshalable_data(net_event.unwrap())
            }
        }),
{
    unimplemented!()
}

pub open spec fn outbound_packet_seq_is_valid(cpackets: Seq<CPacket>) -> bool {
    forall|i| 0 <= i < cpackets.len() ==> #[trigger] outbound_packet_is_valid(&cpackets[i])
}

pub open spec fn outbound_packet_seq_has_correct_srcs(
    cpackets: Seq<CPacket>,
    end_point: AbstractEndPoint,
) -> bool {
    forall|i| #![auto] 0 <= i < cpackets.len() ==> cpackets[i].src@ == end_point
}

pub open spec fn net_packet_bound(data: Seq<u8>) -> bool {
    data.len() <= 0xffff_ffff_ffff_ffff
}

pub open spec fn is_marshalable_data(event: NetEvent) -> bool
    recommends
        event is Send,
{
    &&& net_packet_bound(event.arrow_Send_s().msg)
    &&& sht_demarshal_data(event.arrow_Send_s().msg).is_marshalable()
}

pub open spec fn only_sent_marshalable_data(rawlog: Seq<NetEvent>) -> bool {
    forall|i|
        0 <= i < rawlog.len() && rawlog[i] is Send ==> #[trigger] is_marshalable_data(rawlog[i])
}

pub open spec fn send_log_entries_reflect_packets(
    net_event_log: Seq<NetEvent>,
    cpackets: Seq<CPacket>,
) -> bool {
    &&& net_event_log.len() == cpackets.len()
    &&& (forall|i|
        0 <= i < cpackets.len() ==> #[trigger] send_log_entry_reflects_packet(
            net_event_log[i],
            &cpackets[i],
        ))
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

pub struct LPacket<IdType, MessageType> {
    pub dst: IdType,
    pub src: IdType,
    pub msg: MessageType,
}

pub enum LIoOp<IdType, MessageType> {
    Send { s: LPacket<IdType, MessageType> },
    Receive { r: LPacket<IdType, MessageType> },
    TimeoutReceive {  },
    ReadClock { t: int },
}

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
}

pub struct CKeyKV {
    pub k: CKey,
    pub v: Vec<u8>,
}

pub open spec fn ckeykvlt(a: CKeyKV, b: CKeyKV) -> bool {
    a.k.ukey < b.k.ukey
}

pub open spec fn spec_sorted_keys(v: Vec<CKeyKV>) -> bool {
    forall|i: int, j: int|
        0 <= i && i + 1 < v.len() && j == i + 1 ==> #[trigger] ckeykvlt(v@[i], v@[j])
}

#[derive(PartialEq, Eq, Hash)]
pub struct EndPoint {
    pub id: Vec<u8>,
}

impl EndPoint {
    pub open spec fn view(self) -> AbstractEndPoint {
        AbstractEndPoint { id: self.id@ }
    }

    #[verifier(inline)]
    pub open spec fn abstractable(self) -> bool {
        self@.valid_physical_address()
    }
}

pub enum State {
    Receiving,
    Sending,
    Error,
}

pub struct NetClient {
    state: Ghost<State>,
    history: Ghost<History>,
    end_point: EndPoint,
    c_pointers: NetClientCPointers,
    profiler: DuctTapeProfiler,
}

impl NetClient {
    #[verifier::external_body]
    pub closed spec fn state(&self) -> State {
        unimplemented!()
    }

    pub open spec fn ok(&self) -> bool {
        !(self.state() is Error)
    }

    #[verifier::external_body]
    pub closed spec fn history(&self) -> History {
        unimplemented!()
    }

    #[verifier::external_body]
    pub closed spec fn my_end_point(&self) -> AbstractEndPoint {
        unimplemented!()
    }
}

pub struct KeyIterator<K: KeyTrait + VerusClone> {
    pub k: Option<K>,
}

pub struct KeyRange<K: KeyTrait + VerusClone> {
    pub lo: KeyIterator<K>,
    pub hi: KeyIterator<K>,
}

#[derive(Eq,
    PartialEq, Hash)]
pub struct SHTKey {
    pub ukey: u64,
}

pub enum Message {
    GetRequest { key: AbstractKey },
    SetRequest { key: AbstractKey, value: Option<AbstractValue> },
    Reply { key: AbstractKey, value: Option<AbstractValue> },
    Redirect { key: AbstractKey, id: AbstractEndPoint },
    Shard { range: KeyRange<AbstractKey>, recipient: AbstractEndPoint },
    Delegate { range: KeyRange<AbstractKey>, h: Hashtable },
}

pub struct Packet {
    pub dst: AbstractEndPoint,
    pub src: AbstractEndPoint,
    pub msg: PMsg,
}

pub enum SingleMessage<MT> {
    Message { seqno: nat, dst: AbstractEndPoint, m: MT },
    Ack { ack_seqno: nat },
    InvalidMessage {  },
}

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

pub trait KeyTrait {

}

pub trait VerusClone {

}

impl VerusClone for SHTKey {

}

impl KeyTrait for SHTKey {

}

define_enum_and_derive_marshalable! { pub enum CSingleMessage { #[tag = 0]
    Message { #[o = o0] seqno : u64, #[o = o1] dst : EndPoint, #[o = o2] m : CMessage },
    #[tag = 1] Ack { #[o = o0] ack_seqno : u64 }, #[tag = 2] InvalidMessage, } [rlimit
    attr = verifier::rlimit(25)] }

pub type NetEvent = LIoOp<AbstractEndPoint, Seq<u8>>;

type Ios = Seq<NetEvent>;

pub type AbstractKey = SHTKey;

pub type CKey = SHTKey;

pub type Hashtable = Map<AbstractKey, AbstractValue>;

pub type AbstractValue = Seq<u8>;

type ID = EndPoint;

pub type History = Seq<NetEvent>;

pub type PMsg = SingleMessage<Message>;

pub type NetPacket = LPacket<AbstractEndPoint, Seq<u8>>;

#[verifier(external_body)]
pub struct NetClientCPointers {
    get_time_func: extern "C" fn () -> u64,
    receive_func: extern "C" fn (
        i32,
        *mut bool,
        *mut bool,
        *mut *mut std::vec::Vec<u8>,
        *mut *mut std::vec::Vec<u8>,
    ),
    send_func: extern "C" fn (u64, *const u8, u64, *const u8) -> bool,
}

#[verifier::external_body]
pub struct DuctTapeProfiler {
    last_event: SystemTime,
    last_report: SystemTime,
    event_counter: collections::HashMap<std::string::String, u64>,
}

pub type AbstractIos = Seq<LSHTIo>;

pub type LSHTIo = LIoOp<AbstractEndPoint, SingleMessage<Message>>;

pub type LSHTPacket = LPacket<AbstractEndPoint, SingleMessage<Message>>;

marshalable_by_bijection! {
    [EndPoint] <-> [Vec::< u8 >]; forward(self) self.id; backward(x) EndPoint { id : x };
    }

derive_marshalable_for_enum! { pub enum CMessage { #[tag = 0] GetRequest { #[o =
    o0] k : CKey }, #[tag = 1] SetRequest { #[o = o0] k : CKey, #[o = o1] v : Option::<
    Vec < u8 >> }, #[tag = 2] Reply { #[o = o0] k : CKey, #[o = o1] v : Option::< Vec::<
    u8 >> }, #[tag = 3] Redirect { #[o = o0] k : CKey, #[o = o1] id : EndPoint }, #[tag =
    4] Shard { #[o = o0] kr : KeyRange::< CKey >, #[o = o1] recipient : EndPoint }, #[tag
    = 5] Delegate { #[o = o0] range : KeyRange::< CKey >, #[o = o1] h : CKeyHashMap }, }
    [rlimit attr = verifier::rlimit(20)] }

marshalable_by_bijection! { [KeyRange::< CKey
    >] <-> [(Option::< u64 >, Option::< u64 >)]; forward(self) { (match & self.lo.k {
    None => None, Some(x) => Some(x.ukey), }, match & self.hi.k { None => None, Some(x)
    => Some(x.ukey), },) }; backward(x) { KeyRange { lo : KeyIterator { k : match x.0 {
    None => None, Some(x) => Some(SHTKey { ukey : x }), } }, hi : KeyIterator { k : match
    x.1 { None => None, Some(x) => Some(SHTKey { ukey : x }), } }, } }; }

marshalable_by_bijection! { [SHTKey] <-> [u64]; forward(self) self.ukey; backward(x)
    SHTKey { ukey : x }; }

derive_marshalable_for_struct! { pub struct CKeyKV { pub k :
    CKey, pub v : Vec::< u8 >, } }

#[verifier(spinoff_prover)]
pub fn send_packet_seq(cpackets: &Vec<CPacket>, netc: &mut NetClient) -> (rc: (
    bool,
    Ghost<Seq<NetEvent>>,
))
    requires
        old(netc).ok(),
        outbound_packet_seq_is_valid(cpackets@),
        outbound_packet_seq_has_correct_srcs(cpackets@, old(netc).my_end_point()),
    ensures
        netc.my_end_point() == old(netc).my_end_point(),
        ({
            let (ok, Ghost(net_events)) = rc;
            {
                &&& netc.ok() <==> ok
                &&& ok ==> netc.history() == old(netc).history() + net_events
                &&& ok ==> send_log_entries_reflect_packets(net_events, cpackets@)
                &&& ok ==> only_sent_marshalable_data(net_events)
                &&& forall|i| 0 <= i < net_events.len() ==> net_events[i] is Send
            }
        }),
{
    let ghost ret_ghost0: Seq<NetEvent> = arbitrary(); // TODO - replace with correct value
    let mut i: usize = 0;
    while i < cpackets.len() {
        let cpacket: &CPacket = &cpackets[i];
        let (ok, Ghost(ret_send_packet_ghost0)) = send_packet(cpacket, netc);
        if !ok {
            let ghost ret_ghost0: Seq<NetEvent> = arbitrary(); // TODO - replace with correct value
            let ret = (false, Ghost(ret_ghost0));
            return ret;
        }
        i = i + 1;
    }
    let ret = (true, Ghost(ret_ghost0));
    ret
}

} // verus!
