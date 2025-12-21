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

pub open spec fn abstractify_cmessage_seq(messages: Seq<CSingleMessage>) -> Seq<
    SingleMessage<Message>,
> {
    messages.map_values(|msg: CSingleMessage| msg@)
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

#[allow(unused_macros)]
    macro_rules! derive_marshalable_for_struct { { $(#[$attr : meta])* $pub : vis struct
    $newstruct : ident $(< $($poly : ident : Marshalable),+ $(,)? >)? { $($fieldvis : vis
    $field : ident : $fieldty : ty),+ $(,)? } } => { ::builtin_macros::verus! { impl $(<
    $($poly : Marshalable),* >)? Marshalable for $newstruct $(< $($poly),* >)? { open
    spec fn is_marshalable(& self) -> bool { $(&&& self.$field .is_marshalable())* &&& 0
    $(+ self.$field .ghost_serialize().len())* <= usize::MAX } open spec fn
    ghost_serialize(& self) -> Seq < u8 > { Seq::empty() $(+ self.$field
    .ghost_serialize())* } } } } }

macro_rules! derive_marshalable_for_enum { { $(#[$attr
    : meta])* $pub : vis enum $newenum : ident $(< $($poly : ident : Marshalable),+ $(,)?
    >)? { $(#[tag = $tag : literal] $variant : ident $({ $(#[o =$memother : ident]
    $member : ident : $memberty : ty),* $(,)? })?),+ $(,)? } $([rlimit attr = $rlimitattr
    : meta])? } => { ::builtin_macros::verus! { impl $(< $($poly : Marshalable),+ >)?
    Marshalable for $newenum $(< $($poly),+ >)? { open spec fn is_marshalable(& self) ->
    bool { &&& match self { $($newenum ::$variant $({ $($member),* })? => { $($(&&&
    $member .is_marshalable())*)? &&& 1 $($(+ $member .ghost_serialize().len())*)? <=
    usize::MAX }),+ } } open spec fn ghost_serialize(& self) -> Seq < u8 > { match self {
    $($newenum ::$variant $({ $($member),* })? => { seq![$tag] $($(+ $member
    .ghost_serialize())*)? }),* } } } } } }

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

#[allow(unused_macros)]
    macro_rules! marshalable_by_bijection { { [$type : ty] <-> [$marshalable : ty];
    forward($self : ident) $forward : expr; backward($m : ident) $backward : expr; } => {
    ::builtin_macros::verus! { impl $type { pub open spec fn
    forward_bijection_for_view_equality_do_not_use_for_anything_else($self : Self) ->
    $marshalable { $forward } } impl Marshalable for $type { open spec fn
    is_marshalable($self : & Self) -> bool { $forward .is_marshalable() } open spec fn
    ghost_serialize($self : & Self) -> Seq < u8 > { $forward .ghost_serialize() } } } } }

impl Ordering {
    pub open spec fn lt(self) -> bool {
        matches!(self, Ordering::Less)
    }
}

impl<K: KeyTrait + VerusClone> KeyIterator<K> {
    pub open spec fn between(lhs: Self, ki: Self, rhs: Self) -> bool {
        !ki.lt_spec(lhs) && ki.lt_spec(rhs)
    }
}

#[verifier::reject_recursive_types(K)]
pub struct DelegationMap<K: KeyTrait + VerusClone> {
    lows: StrictlyOrderedMap<K>,
    m: Ghost<Map<K, AbstractEndPoint>>,
}

impl<K: KeyTrait + VerusClone> DelegationMap<K> {
    #[verifier::external_body]
    pub closed spec fn view(self) -> Map<K, AbstractEndPoint> {
        unimplemented!()
    }

    #[verifier::external_body]
    pub closed spec fn valid(self) -> bool {
        unimplemented!()
    }
}

pub struct Constants {
    pub root_identity: EndPoint,
    pub host_ids: Vec<EndPoint>,
    pub params: Parameters,
    pub me: EndPoint,
}

impl Constants {
    pub open spec fn view(self) -> AbstractConstants {
        AbstractConstants {
            root_identity: self.root_identity@,
            host_ids: abstractify_end_points(self.host_ids),
            params: self.params@,
            me: self.me@,
        }
    }

    pub closed spec fn abstractable(self) -> bool {
        true
    }

    pub closed spec fn valid(self) -> bool {
        &&& self.params.valid()
        &&& seq_is_unique(abstractify_end_points(self.host_ids))
        &&& self.root_identity@.valid_physical_address()
    }
}

pub struct Parameters {
    pub max_seqno: u64,
    pub max_delegations: u64,
}

impl Parameters {
    pub open spec fn view(self) -> AbstractParameters {
        AbstractParameters {
            max_seqno: self.max_seqno as nat,
            max_delegations: self.max_delegations as nat,
        }
    }

    pub open spec fn valid(self) -> bool {
        &&& self.max_seqno == 0xffff_ffff_ffff_ffff
        &&& 3 < self.max_delegations
        &&& self.max_delegations < 0x8000_0000_0000_0000
    }
}

pub open spec fn abstractify_cpacket_to_lsht_packet(cp: CPacket) -> LSHTPacket
    recommends
        cp.abstractable(),
{
    LPacket { dst: cp.dst@, src: cp.src@, msg: cp.msg@ }
}

pub open spec fn abstractify_raw_log_to_ios(rawlog: Seq<NetEvent>) -> Seq<LSHTIo> {
    rawlog.map_values(|evt: NetEvent| abstractify_net_event_to_lsht_io(evt))
}

pub open spec fn raw_io_consistent_with_spec_io(rawlog: Seq<NetEvent>, ios: Seq<LSHTIo>) -> bool {
    &&& net_event_log_is_abstractable(rawlog)
    &&& abstractify_raw_log_to_ios(rawlog) == ios
}

pub struct HostState {
    next_action_index: u64,
    resend_count: u64,
    constants: Constants,
    delegation_map: DelegationMap<CKey>,
    h: CKeyHashMap,
    sd: CSingleDelivery,
    received_packet: Option<CPacket>,
    num_delegations: u64,
    received_requests: Ghost<Seq<AppRequest>>,
}

pub enum ReceiveResult {
    Fail,
    Timeout,
    Packet { cpacket: CPacket },
}

pub open spec fn net_packet_is_abstractable(net: NetPacket) -> bool {
    true
}

pub open spec fn net_event_is_abstractable(evt: NetEvent) -> bool {
    match evt {
        LIoOp::<AbstractEndPoint, Seq<u8>>::Send { s } => net_packet_is_abstractable(s),
        LIoOp::<AbstractEndPoint, Seq<u8>>::Receive { r } => net_packet_is_abstractable(r),
        LIoOp::<AbstractEndPoint, Seq<u8>>::TimeoutReceive {  } => true,
        LIoOp::<AbstractEndPoint, Seq<u8>>::ReadClock { t } => true,
    }
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

pub open spec fn abstractify_net_event_to_lsht_io(evt: NetEvent) -> LSHTIo
    recommends
        net_event_is_abstractable(evt),
{
    match evt {
        LIoOp::<AbstractEndPoint, Seq<u8>>::Send { s } => LIoOp::<
            AbstractEndPoint,
            SingleMessage<Message>,
        >::Send { s: abstractify_net_packet_to_lsht_packet(s) },
        LIoOp::<AbstractEndPoint, Seq<u8>>::Receive { r } => LIoOp::<
            AbstractEndPoint,
            SingleMessage<Message>,
        >::Receive { r: abstractify_net_packet_to_lsht_packet(r) },
        LIoOp::<AbstractEndPoint, Seq<u8>>::TimeoutReceive {  } => LIoOp::<
            AbstractEndPoint,
            SingleMessage<Message>,
        >::TimeoutReceive {  },
        LIoOp::<AbstractEndPoint, Seq<u8>>::ReadClock { t } => LIoOp::<
            AbstractEndPoint,
            SingleMessage<Message>,
        >::ReadClock { t: t as int },
    }
}

pub open spec fn abstractify_net_packet_to_sht_packet(net: NetPacket) -> Packet
    recommends
        net_packet_is_abstractable(net),
{
    let lp = abstractify_net_packet_to_lsht_packet(net);
    Packet { dst: lp.dst, src: lp.src, msg: lp.msg }
}

pub open spec fn net_event_log_is_abstractable(rawlog: Seq<NetEvent>) -> bool {
    forall|i: int| 0 <= i && i < rawlog.len() ==> #[trigger] net_event_is_abstractable(rawlog[i])
}

#[verifier::external_body]
pub fn receive_with_demarshal(netc: &mut NetClient, local_addr: &EndPoint) -> (rc: (
    ReceiveResult,
    Ghost<NetEvent>,
))
    requires
        old(netc).ok(),
        old(netc).my_end_point() == local_addr@,
        old(netc).state() is Receiving,
        local_addr.abstractable(),
    ensures
        ({
            let (rr, net_event) = rc;
            &&& netc.my_end_point() == old(netc).my_end_point()
            &&& netc.ok() == !(rr is Fail)
            &&& !(rr is Fail) ==> netc.ok() && netc.history() == old(netc).history()
                + seq!(net_event @)
            &&& rr is Timeout ==> net_event@ is TimeoutReceive
            &&& (rr is Packet ==> {
                &&& net_event@ is Receive
                &&& true
                &&& rr.arrow_Packet_cpacket().abstractable()
                &&& true
                &&& !(rr.arrow_Packet_cpacket()@.msg is InvalidMessage) ==> {
                    &&& rr.arrow_Packet_cpacket()@ == abstractify_net_packet_to_sht_packet(
                        net_event@.arrow_Receive_r(),
                    )
                    &&& rr.arrow_Packet_cpacket().msg@ == sht_demarshal_data(
                        net_event@.arrow_Receive_r().msg,
                    )@
                }
                &&& rr.arrow_Packet_cpacket().dst@ == local_addr@
            })
        }),
{
    unimplemented!()
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

    pub open spec fn abstractable(&self) -> bool {
        forall|i: int| 0 <= i < self.un_acked.len() ==> #[trigger] self.un_acked[i].abstractable()
    }

    pub open spec fn no_acks_in_unacked(list: Seq<CSingleMessage>) -> bool {
        forall|i: int| 0 <= i < list.len() ==> #[trigger] list[i] is Message
    }

    pub open spec fn un_acked_list_sequential(list: Seq<CSingleMessage>) -> bool
        recommends
            Self::no_acks_in_unacked(list),
    {
        forall|i: int, j: int|
            #![auto]
            0 <= i && j == i + 1 && j < list.len() ==> list[i].arrow_Message_seqno() as int + 1
                == list[j].arrow_Message_seqno() as int
    }

    pub open spec fn un_acked_valid(msg: &CSingleMessage) -> bool {
        &&& msg is Message
        &&& msg.abstractable()
        &&& msg.is_marshalable()
    }

    pub open spec fn un_acked_list_valid(list: Seq<CSingleMessage>) -> bool {
        &&& forall|i: int| 0 <= i < list.len() ==> #[trigger] Self::un_acked_valid(&list[i])
        &&& Self::un_acked_list_sequential(list)
    }

    pub open spec fn un_acked_list_valid_for_dst(
        list: Seq<CSingleMessage>,
        dst: AbstractEndPoint,
    ) -> bool {
        &&& Self::un_acked_list_valid(list)
        &&& forall|i: int| 0 <= i < list.len() ==> (#[trigger] list[i].arrow_Message_dst())@ == dst
    }

    pub open spec fn valid_list(
        msgs: Seq<CSingleMessage>,
        num_packets_acked: int,
        dst: AbstractEndPoint,
    ) -> bool {
        &&& Self::un_acked_list_valid_for_dst(msgs, dst)
        &&& num_packets_acked as int + msgs.len() as int
            <= AbstractParameters::static_params().max_seqno
        &&& (msgs.len() > 0 ==> msgs[0].arrow_Message_seqno() == num_packets_acked + 1)
    }

    pub open spec fn valid(&self, dst: AbstractEndPoint) -> bool {
        &&& self.abstractable()
        &&& Self::valid_list(self.un_acked@, self.num_packets_acked as int, dst)
    }
}

pub struct CTombstoneTable {
    pub epmap: HashMap<u64>,
}

impl CTombstoneTable {
    pub open spec fn abstractable(&self) -> bool {
        forall|k: AbstractEndPoint| #[trigger] self@.contains_key(k) ==> k.valid_physical_address()
    }

    pub open spec fn view(&self) -> TombstoneTable {
        self.epmap@.map_values(|v: u64| v as nat)
    }
}

pub struct CSendState {
    pub epmap: HashMap<CAckState>,
}

impl CSendState {
    pub open spec fn abstractable(&self) -> bool {
        forall|ep: EndPoint| #[trigger]
            self@.contains_key(ep@) ==> ep.abstractable() && self.epmap[&ep].abstractable()
    }

    pub open spec fn valid(&self) -> bool {
        &&& self.abstractable()
        &&& forall|ep: AbstractEndPoint| #[trigger]
            self@.contains_key(ep) ==> self.epmap@[ep].valid(ep)
    }

    pub open spec fn view(&self) -> SendState<Message> {
        self.epmap@.map_values(|v: CAckState| v@)
    }
}

pub struct CSingleDelivery {
    pub receive_state: CTombstoneTable,
    pub send_state: CSendState,
}

impl CSingleDelivery {
    pub open spec fn abstractable(&self) -> bool {
        &&& self.receive_state.abstractable()
        &&& self.send_state.abstractable()
    }

    pub open spec fn view(self) -> SingleDelivery<Message> {
        SingleDelivery { receive_state: self.receive_state@, send_state: self.send_state@ }
    }

    pub open spec fn valid(&self) -> bool {
        &&& self.abstractable()
        &&& self.send_state.valid()
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

pub struct AbstractParameters {
    pub max_seqno: nat,
    pub max_delegations: nat,
}

impl AbstractParameters {
    pub open spec fn static_params() -> AbstractParameters {
        AbstractParameters {
            max_seqno: 0xffff_ffff_ffff_ffff as nat,
            max_delegations: 0x7FFF_FFFF_FFFF_FFFF as nat,
        }
    }
}

pub enum AppRequest {
    AppGetRequest { seqno: nat, key: AbstractKey },
    AppSetRequest { seqno: nat, key: AbstractKey, ov: Option<AbstractValue> },
}

#[verifier::ext_equal]
pub struct AbstractDelegationMap(pub Map<AbstractKey, AbstractEndPoint>);

impl AbstractDelegationMap {
    #[verifier(inline)]
    pub open spec fn view(self) -> Map<AbstractKey, AbstractEndPoint> {
        self.0
    }

    #[verifier(inline)]
    pub open spec fn spec_index(self, key: AbstractKey) -> AbstractEndPoint
        recommends
            self.0.dom().contains(key),
    {
        self@.index(key)
    }

    pub open spec fn is_complete(self) -> bool {
        self@.dom().is_full()
    }

    pub open spec fn update(self, newkr: KeyRange<AbstractKey>, host: AbstractEndPoint) -> Self
        recommends
            self.is_complete(),
    {
        AbstractDelegationMap(self@.union_prefer_right(Map::new(|k| newkr.contains(k), |k| host)))
    }

    pub open spec fn delegate_for_key_range_is_host(
        self,
        kr: KeyRange<AbstractKey>,
        id: AbstractEndPoint,
    ) -> bool
        recommends
            self.is_complete(),
    {
        forall|k: AbstractKey| #[trigger] kr.contains(k) ==> self[k] == id
    }
}

#[verifier::accept_recursive_types(V)]
#[verifier(external_body)]
pub struct HashMap<V> {
    m: collections::HashMap<EndPoint, V>,
}

impl<V> HashMap<V> {
    pub uninterp spec fn view(self) -> Map<AbstractEndPoint, V>;

    pub open spec fn spec_index(self, key: &EndPoint) -> V
        recommends
            self@.contains_key(key@),
    {
        self@[key@]
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
    pub fn to_vec(&self) -> (res: Vec<CKeyKV>)
        ensures
            res == self.spec_to_vec(),
    {
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

pub struct EventResults {
    pub recvs: Seq<NetEvent>,
    pub clocks: Seq<NetEvent>,
    pub sends: Seq<NetEvent>,
    #[doc
    = " What we were trying to make happen:"]
    #[doc =
    " ios may claim an event that doesn't appear in event_seq() if, say, the netc socket broke on"]
    #[doc =
    " send. We already received, so the only way we can refine is by claiming we finished the"]
    #[doc =
    " corresponding send (in ios). In this case, the postcondition of next_ensures gives"]
    #[doc = " us the out because !netc.ok allows ios!=event_seq()."]
    pub ios: Ios,
}

impl EventResults {
    pub open spec fn event_seq(self) -> Seq<NetEvent> {
        self.recvs + self.clocks + self.sends
    }

    pub open spec fn well_typed_events(self) -> bool {
        &&& forall|i| 0 <= i < self.recvs.len() ==> self.recvs[i] is Receive
        &&& forall|i|
            0 <= i < self.clocks.len() ==> self.clocks[i] is ReadClock
                || self.clocks[i] is TimeoutReceive
        &&& forall|i| 0 <= i < self.sends.len() ==> self.sends[i] is Send
        &&& self.clocks.len() <= 1
    }
}

impl HostState {
    pub open spec fn next_requires(self, netc: NetClient) -> bool {
        &&& self.invariants(&netc.my_end_point())
        &&& netc.state() is Receiving
    }

    pub open spec fn next_ensures(
        old_self: Self,
        old_netc: NetClient,
        new_self: Self,
        new_netc: NetClient,
        rc: (bool, Ghost<EventResults>),
    ) -> bool {
        let (ok, res) = rc;
        {
            &&& ok == new_netc.ok()
            &&& ok ==> new_self.invariants(&new_netc.my_end_point())
            &&& ok ==> Self::next(old_self.view(), new_self.view(), res@.ios)
            &&& ok ==> res@.event_seq() == res@.ios
            &&& (ok || res@.sends.len() > 0) ==> new_netc.history() == old_netc.history()
                + res@.event_seq()
            &&& res@.well_typed_events()
        }
    }

    pub open spec fn next(pre: AbstractHostState, post: AbstractHostState, ios: Ios) -> bool {
        next(pre, post, abstractify_raw_log_to_ios(ios))
    }
}

pub struct AbstractConstants {
    pub root_identity: AbstractEndPoint,
    pub host_ids: Seq<AbstractEndPoint>,
    pub params: AbstractParameters,
    pub me: AbstractEndPoint,
}

pub struct AbstractHostState {
    pub constants: AbstractConstants,
    pub delegation_map: AbstractDelegationMap,
    pub h: Hashtable,
    pub sd: SingleDelivery<Message>,
    pub received_packet: Option<Packet>,
    pub num_delegations: int,
    pub received_requests: Seq<AppRequest>,
}

impl AbstractHostState {
    pub open spec(checked) fn wf(self) -> bool {
        &&& self.delegation_map.is_complete()
    }
}

pub open spec fn max_hashtable_size() -> int {
    62
}

pub open spec fn valid_hashtable(h: Hashtable) -> bool {
    &&& h.dom().len() < max_hashtable_size()
    &&& (forall|k| h.dom().contains(k) ==> valid_key(k) && #[trigger] valid_value(h[k]))
}

pub open spec(checked) fn hashtable_lookup(h: Hashtable, k: AbstractKey) -> Option<AbstractValue> {
    if h.dom().contains(k) {
        Some(h[k])
    } else {
        None
    }
}

pub open spec(checked) fn bulk_update_domain(
    h: Hashtable,
    kr: KeyRange<AbstractKey>,
    u: Hashtable,
) -> Set<AbstractKey> {
    Set::<AbstractKey>::new(
        |k|
            (h.dom().contains(k) || u.dom().contains(k)) && (kr.contains(k) ==> u.dom().contains(
                k,
            )),
    )
}

pub open spec fn bulk_update_hashtable(
    h: Hashtable,
    kr: KeyRange<AbstractKey>,
    u: Hashtable,
) -> Hashtable {
    Map::<AbstractKey, AbstractValue>::new(
        |k: AbstractKey| bulk_update_domain(h, kr, u).contains(k),
        |k: AbstractKey|
            if u.dom().contains(k) {
                u[k]
            } else {
                h[k]
            },
    )
}

pub open spec fn bulk_remove_hashtable(h: Hashtable, kr: KeyRange<AbstractKey>) -> Hashtable {
    Map::<AbstractKey, AbstractValue>::new(
        |k: AbstractKey| h.dom().contains(k) && !kr.contains(k),
        |k: AbstractKey| h[k],
    )
}

pub open spec(checked) fn valid_optional_value(ov: Option<AbstractValue>) -> bool {
    match ov {
        None => true,
        Some(value) => valid_value(value),
    }
}

#[verifier::opaque]
pub open spec fn okay_to_ignore_packets() -> bool {
    true
}

pub open spec(checked) fn receive_packet(
    pre: AbstractHostState,
    post: AbstractHostState,
    pkt: Packet,
    out: Set<Packet>,
    ack: Packet,
) -> bool {
    ||| {
        &&& pre.received_packet is None
        &&& SingleDelivery::receive(pre.sd, post.sd, pkt, ack, out)
        &&& if SingleDelivery::new_single_message(pre.sd, pkt) {
            post.received_packet == Some(pkt)
        } else {
            post.received_packet is None
        }
        &&& post == AbstractHostState { sd: post.sd, received_packet: post.received_packet, ..post }
    }
    ||| {
        &&& pre.received_packet is Some || okay_to_ignore_packets()
        &&& post == pre
        &&& out == Set::<Packet>::empty()
    }
}

pub open spec fn extract_sent_packets_from_ios(ios: Seq<LSHTIo>) -> Seq<LSHTPacket> {
    ios.filter(|io: LSHTIo| io is Send).map_values(|io: LSHTIo| io.arrow_Send_s())
}

pub open spec fn extract_packet_from_lsht_packet(lp: LSHTPacket) -> Packet {
    Packet { dst: lp.dst, src: lp.src, msg: lp.msg }
}

pub open spec fn extract_packets_from_lsht_packets(seq_packets: Seq<LSHTPacket>) -> Set<Packet> {
    seq_packets.map_values(|lp: LSHTPacket| extract_packet_from_lsht_packet(lp)).to_set()
}

pub open spec fn extract_packets_from_abstract_ios(ios: AbstractIos) -> Set<Packet> {
    extract_packets_from_lsht_packets(extract_sent_packets_from_ios(ios))
}

pub open spec(checked) fn receive_packet_wrapper(
    pre: AbstractHostState,
    post: AbstractHostState,
    pkt: Packet,
    sent_packets: Set<Packet>,
) -> bool {
    exists|ack| receive_packet(pre, post, pkt, sent_packets, ack)
}

pub open spec(checked) fn receive_packet_without_reading_clock(
    pre: AbstractHostState,
    post: AbstractHostState,
    ios: AbstractIos,
) -> bool
    recommends
        ios.len() >= 1,
        ios[0] is Receive,
        pre.delegation_map.is_complete(),
{
    let r = ios[0].arrow_Receive_r();
    let pkt = Packet { dst: r.dst, src: r.src, msg: r.msg };
    let sent_packets = extract_packets_from_abstract_ios(ios);
    receive_packet_wrapper(pre, post, pkt, sent_packets)
}

pub open spec(checked) fn receive_packet_next(
    pre: AbstractHostState,
    post: AbstractHostState,
    ios: AbstractIos,
) -> bool {
    &&& ios.len() >= 1
    &&& if ios[0] is TimeoutReceive {
        &&& post == pre
        &&& ios.len() == 1
    } else {
        &&& pre.delegation_map.is_complete()
        &&& ios[0] is Receive
        &&& forall|i| 1 <= i < ios.len() ==> ios[i] is Send
        &&& receive_packet_without_reading_clock(pre, post, ios)
    }
}

pub open spec(checked) fn next_get_request_reply(
    pre: AbstractHostState,
    post: AbstractHostState,
    src: AbstractEndPoint,
    seqno: nat,
    k: AbstractKey,
    sm: SingleMessage<Message>,
    m: Message,
    out: Set<Packet>,
    should_send: bool,
) -> bool
    recommends
        pre.delegation_map.is_complete(),
{
    let owner = pre.delegation_map[k];
    if should_send && valid_key(k) {
        &&& if owner == pre.constants.me {
            &&& m == Message::Reply { key: k, value: hashtable_lookup(pre.h, k) }
            &&& post.received_requests == pre.received_requests.push(
                AppRequest::AppGetRequest { seqno, key: k },
            )
        } else {
            &&& m == Message::Redirect { key: k, id: owner }
            &&& post.received_requests == pre.received_requests
        }
        &&& SingleDelivery::send_single_message(
            pre.sd,
            post.sd,
            m,
            src,
            Some(sm),
            pre.constants.params,
        )
        &&& sm.arrow_Message_dst() == src
        &&& out == set![Packet { dst : src, src :
    pre.constants.me, msg : sm }]
    } else {
        &&& post == AbstractHostState { received_packet: post.received_packet, ..pre }
        &&& out == Set::<Packet>::empty()
    }
}

pub open spec(checked) fn next_get_request(
    pre: AbstractHostState,
    post: AbstractHostState,
    pkt: Packet,
    out: Set<Packet>,
) -> bool
    recommends
        pkt.msg is Message,
        pre.delegation_map.is_complete(),
{
    &&& pkt.msg.arrow_Message_m() is GetRequest
    &&& post.delegation_map == pre.delegation_map
    &&& post.h == pre.h
    &&& post.num_delegations == pre.num_delegations
    &&& (exists|sm, m, b|
        next_get_request_reply(
            pre,
            post,
            pkt.src,
            pkt.msg.arrow_Message_seqno(),
            pkt.msg.arrow_Message_m().arrow_GetRequest_key(),
            sm,
            m,
            out,
            b,
        ))
}

pub open spec(checked) fn next_set_request_complete(
    pre: AbstractHostState,
    post: AbstractHostState,
    src: AbstractEndPoint,
    seqno: nat,
    reqm: Message,
    sm: SingleMessage<Message>,
    replym: Message,
    out: Set<Packet>,
    should_send: bool,
) -> bool
    recommends
        pre.delegation_map.is_complete(),
        reqm is SetRequest,
{
    let k = reqm.arrow_SetRequest_key();
    let ov = reqm.arrow_SetRequest_value();
    let owner = pre.delegation_map[k];
    if should_send && valid_key(k) && valid_optional_value(ov) {
        &&& if owner == pre.constants.me {
            &&& post.h == match ov {
                None => pre.h.remove(k),
                Some(v) => pre.h.insert(k, v),
            }
            &&& replym == Message::Reply { key: k, value: ov }
            &&& post.received_requests == pre.received_requests.push(
                AppRequest::AppSetRequest { seqno: seqno, key: k, ov: ov },
            )
        } else {
            &&& post.h == pre.h
            &&& replym == Message::Redirect { key: k, id: owner }
            &&& post.received_requests == pre.received_requests
        }
        &&& SingleDelivery::send_single_message(
            pre.sd,
            post.sd,
            replym,
            src,
            Some(sm),
            pre.constants.params,
        )
        &&& sm.arrow_Message_dst() == src
        &&& out == set![Packet { dst : src, src : pre.constants.me, msg : sm }]
    } else {
        &&& post == AbstractHostState { received_packet: post.received_packet, ..pre }
        &&& out == Set::<Packet>::empty()
    }
}

pub open spec(checked) fn next_set_request(
    pre: AbstractHostState,
    post: AbstractHostState,
    pkt: Packet,
    out: Set<Packet>,
) -> bool
    recommends
        pkt.msg is Message,
        pre.delegation_map.is_complete(),
{
    &&& pkt.msg.arrow_Message_m() is SetRequest
    &&& exists|sm: SingleMessage<Message>, replym: Message, should_send: bool|
        next_set_request_complete(
            pre,
            post,
            pkt.src,
            pkt.msg.arrow_Message_seqno(),
            pkt.msg.arrow_Message_m(),
            sm,
            replym,
            out,
            should_send,
        )
    &&& post.delegation_map == pre.delegation_map
    &&& post.num_delegations == pre.num_delegations
}

pub open spec(checked) fn next_delegate(
    pre: AbstractHostState,
    post: AbstractHostState,
    pkt: Packet,
    out: Set<Packet>,
) -> bool
    recommends
        pkt.msg is Message,
        pre.delegation_map.is_complete(),
{
    &&& pkt.msg.arrow_Message_m() is Delegate
    &&& if pre.constants.host_ids.contains(pkt.src) {
        let m = pkt.msg.arrow_Message_m();
        &&& post.delegation_map == pre.delegation_map.update(
            m.arrow_Delegate_range(),
            pre.constants.me,
        )
        &&& post.h == bulk_update_hashtable(pre.h, m.arrow_Delegate_range(), m.arrow_Delegate_h())
        &&& post.num_delegations == pre.num_delegations + 1
    } else {
        &&& post.delegation_map == pre.delegation_map
        &&& post.h == pre.h
        &&& post.num_delegations == pre.num_delegations
    }
    &&& SingleDelivery::<Message>::send_no_message(pre.sd, post.sd)
    &&& SingleDelivery::<Message>::receive_no_message(pre.sd, post.sd)
    &&& out == Set::<Packet>::empty()
    &&& post.received_requests == pre.received_requests
}

pub open spec(checked) fn next_shard(
    pre: AbstractHostState,
    post: AbstractHostState,
    out: Set<Packet>,
    kr: KeyRange<AbstractKey>,
    recipient: AbstractEndPoint,
    sm: SingleMessage<Message>,
    should_send: bool,
) -> bool
    recommends
        pre.delegation_map.is_complete(),
{
    &&& recipient != pre.constants.me
    &&& pre.constants.host_ids.contains(recipient)
    &&& pre.delegation_map.delegate_for_key_range_is_host(kr, pre.constants.me)
    &&& SingleDelivery::send_single_message(
        pre.sd,
        post.sd,
        Message::Delegate { range: kr, h: extract_range(pre.h, kr) },
        recipient,
        if should_send {
            Some(sm)
        } else {
            None
        },
        pre.constants.params,
    )
    &&& should_send ==> recipient == sm.arrow_Message_dst()
    &&& pre.constants == post.constants
    &&& post.num_delegations == pre.num_delegations + 1
    &&& post.received_requests == pre.received_requests
    &&& if should_send {
        &&& out == set![Packet { dst : recipient, src : pre.constants.me, msg : sm }]
        &&& post.delegation_map == pre.delegation_map.update(kr, recipient)
        &&& post.h == bulk_remove_hashtable(pre.h, kr)
    } else {
        &&& out == Set::<Packet>::empty()
        &&& post.delegation_map == pre.delegation_map
        &&& post.h == pre.h
    }
}

pub open spec fn next_shard_wrapper_must_reject(pre: AbstractHostState, m: Message) -> bool {
    let recipient = m.arrow_Shard_recipient();
    let kr = m.arrow_Shard_range();
    ||| recipient == pre.constants.me
    ||| !recipient.valid_physical_address()
    ||| kr.is_empty()
    ||| !pre.constants.host_ids.contains(recipient)
    ||| !pre.delegation_map.delegate_for_key_range_is_host(kr, pre.constants.me)
    ||| extract_range(pre.h, kr).dom().len() >= max_hashtable_size()
}

pub open spec(checked) fn next_shard_wrapper(
    pre: AbstractHostState,
    post: AbstractHostState,
    pkt: Packet,
    out: Set<Packet>,
) -> bool
    recommends
        pkt.msg is Message,
        pre.delegation_map.is_complete(),
{
    let m: Message = pkt.msg.arrow_Message_m();
    let recipient = m.arrow_Shard_recipient();
    let kr = m.arrow_Shard_range();
    &&& m is Shard
    &&& if next_shard_wrapper_must_reject(pre, m) {
        &&& post == AbstractHostState { received_packet: post.received_packet, ..pre }
        &&& out == Set::<Packet>::empty()
    } else {
        exists|sm: SingleMessage<Message>, b: bool| next_shard(pre, post, out, kr, recipient, sm, b)
    }
}

pub open spec(checked) fn next_reply(
    pre: AbstractHostState,
    post: AbstractHostState,
    pkt: Packet,
    out: Set<Packet>,
) -> bool
    recommends
        pkt.msg is Message,
        pre.delegation_map.is_complete(),
{
    &&& pkt.msg.arrow_Message_m() is Reply
    &&& out == Set::<Packet>::empty()
    &&& post == AbstractHostState { received_packet: post.received_packet, ..pre }
}

pub open spec(checked) fn next_redirect(
    pre: AbstractHostState,
    post: AbstractHostState,
    pkt: Packet,
    out: Set<Packet>,
) -> bool
    recommends
        pkt.msg is Message,
        pre.delegation_map.is_complete(),
{
    &&& pkt.msg.arrow_Message_m() is Redirect
    &&& out == Set::<Packet>::empty()
    &&& post == AbstractHostState { received_packet: post.received_packet, ..pre }
}

pub open spec(checked) fn should_process_received_message(pre: AbstractHostState) -> bool {
    &&& pre.received_packet.is_some()
    &&& pre.received_packet.arrow_Some_0().msg is Message
    &&& {
        ||| pre.received_packet.arrow_Some_0().msg.arrow_Message_m() is Delegate
        ||| pre.received_packet.arrow_Some_0().msg.arrow_Message_m() is Shard
    } ==> pre.num_delegations < pre.constants.params.max_delegations - 2
}

pub open spec(checked) fn process_message(
    pre: AbstractHostState,
    post: AbstractHostState,
    out: Set<Packet>,
) -> bool
    recommends
        pre.delegation_map.is_complete(),
{
    if should_process_received_message(pre) {
        let packet = pre.received_packet.arrow_Some_0();
        &&& {
            ||| next_get_request(pre, post, packet, out)
            ||| next_set_request(pre, post, packet, out)
            ||| next_delegate(pre, post, packet, out)
            ||| next_shard_wrapper(pre, post, packet, out)
            ||| next_reply(pre, post, packet, out)
            ||| next_redirect(pre, post, packet, out)
        }
        &&& post.received_packet is None
    } else {
        &&& post == pre
        &&& out == Set::<Packet>::empty()
    }
}

pub open spec(checked) fn process_received_packet(
    pre: AbstractHostState,
    post: AbstractHostState,
    out: Set<Packet>,
) -> bool
    recommends
        pre.delegation_map.is_complete(),
{
    match pre.received_packet {
        Some(_) => process_message(pre, post, out),
        None => {
            &&& post == pre
            &&& out == Set::<Packet>::empty()
        },
    }
}

pub open spec(checked) fn process_received_packet_next(
    pre: AbstractHostState,
    post: AbstractHostState,
    ios: AbstractIos,
) -> bool {
    &&& pre.delegation_map.is_complete()
    &&& forall|i| 0 <= i < ios.len() ==> ios[i] is Send
    &&& process_received_packet(pre, post, extract_packets_from_abstract_ios(ios))
}

pub open spec(checked) fn spontaneously_retransmit(
    pre: AbstractHostState,
    post: AbstractHostState,
    out: Set<Packet>,
) -> bool {
    &&& out == SingleDelivery::un_acked_messages(pre.sd, pre.constants.me)
    &&& post == pre
}

pub open spec(checked) fn spontaneously_retransmit_next(
    pre: AbstractHostState,
    post: AbstractHostState,
    ios: AbstractIos,
) -> bool {
    &&& pre.delegation_map.is_complete()
    &&& {
        ||| {
            &&& forall|i| 0 <= i < ios.len() ==> ios[i] is Send
            &&& spontaneously_retransmit(pre, post, extract_packets_from_abstract_ios(ios))
        }
        ||| {
            &&& post == pre
            &&& ios =~= Seq::<LSHTIo>::empty()
        }
    }
}

pub open spec(checked) fn ignore_unparseable_packet(
    pre: AbstractHostState,
    post: AbstractHostState,
    ios: AbstractIos,
) -> bool {
    &&& ios.len() == 1
    &&& ios[0] is Receive
    &&& ios[0].arrow_Receive_r().msg is InvalidMessage
    &&& pre == post
}

pub open spec(checked) fn ignore_nonsensical_delegation_packet(
    pre: AbstractHostState,
    post: AbstractHostState,
    ios: AbstractIos,
) -> bool {
    &&& ios.len() == 0
    &&& pre.received_packet.is_some()
    &&& pre.received_packet.arrow_Some_0().msg is Message
    &&& match pre.received_packet.arrow_Some_0().msg.arrow_Message_m() {
        Message::Delegate { range: range, h: h } => !({
            &&& valid_hashtable(h)
            &&& !range.is_empty()
            &&& pre.received_packet.arrow_Some_0().msg.arrow_Message_dst().valid_physical_address()
        }),
        _ => false,
    }
    &&& if should_process_received_message(pre) {
        post == AbstractHostState { received_packet: None, ..pre }
    } else {
        post == pre
    }
}

pub enum Step {
    ReceivePacket,
    ProcessReceivedPacket,
    SpontaneouslyRetransmit,
    Stutter,
    IgnoreUnparseablePacket,
    IgnoreNonsensicalDelegationPacket,
}

pub open spec(checked) fn next_step(
    pre: AbstractHostState,
    post: AbstractHostState,
    ios: AbstractIos,
    step: Step,
) -> bool {
    &&& pre.delegation_map.is_complete()
    &&& match step {
        Step::ReceivePacket => receive_packet_next(pre, post, ios),
        Step::ProcessReceivedPacket => process_received_packet_next(pre, post, ios),
        Step::SpontaneouslyRetransmit => spontaneously_retransmit_next(pre, post, ios),
        Step::Stutter => pre == post && ios.len() == 0,
        Step::IgnoreUnparseablePacket => ignore_unparseable_packet(pre, post, ios),
        Step::IgnoreNonsensicalDelegationPacket => ignore_nonsensical_delegation_packet(
            pre,
            post,
            ios,
        ),
    }
}

pub open spec(checked) fn no_invalid_sends(ios: AbstractIos) -> bool {
    forall|i|
        #![auto]
        0 <= i < ios.len() && ios[i] is Send ==> !(ios[i].arrow_Send_s().msg is InvalidMessage)
}

pub open spec(checked) fn next(
    pre: AbstractHostState,
    post: AbstractHostState,
    ios: AbstractIos,
) -> bool {
    &&& pre.wf()
    &&& pre.constants == post.constants
    &&& exists|step| next_step(pre, post, ios, step)
    &&& no_invalid_sends(ios)
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

pub open spec fn abstractify_end_points(end_points: Vec<EndPoint>) -> Seq<AbstractEndPoint> {
    end_points@.map(|i, end_point: EndPoint| end_point@)
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

pub trait KeyTrait: Sized {
    spec fn cmp_spec(self, other: Self) -> Ordering;
}

#[derive(Structural, PartialEq, Eq)]
pub enum Ordering {
    Less,
    Equal,
    Greater,
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

pub struct KeyRange<K: KeyTrait + VerusClone> {
    pub lo: KeyIterator<K>,
    pub hi: KeyIterator<K>,
}

impl<K: KeyTrait + VerusClone> KeyRange<K> {
    pub open spec fn contains(self, k: K) -> bool {
        KeyIterator::<K>::between(self.lo, KeyIterator::<K>::new_spec(k), self.hi)
    }

    pub open spec fn is_empty(self) -> bool {
        self.lo.geq_spec(self.hi)
    }
}

#[derive(Eq,
    PartialEq, Hash)]
pub struct SHTKey {
    pub ukey: u64,
}

impl KeyTrait for SHTKey {
    open spec fn cmp_spec(self, other: Self) -> Ordering {
        if self.ukey < other.ukey {
            Ordering::Less
        } else if self.ukey == other.ukey {
            Ordering::Equal
        } else {
            Ordering::Greater
        }
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

pub struct Packet {
    pub dst: AbstractEndPoint,
    pub src: AbstractEndPoint,
    pub msg: PMsg,
}

pub open spec fn tombstone_table_lookup(src: AbstractEndPoint, t: TombstoneTable) -> nat {
    if t.dom().contains(src) {
        t[src]
    } else {
        0
    }
}

pub open spec(checked) fn truncate_un_ack_list<MT>(un_acked: AckList<MT>, seqno_acked: nat) -> Seq<
    SingleMessage<MT>,
>
    decreases un_acked.len(),
{
    if un_acked.len() > 0 && un_acked[0] is Message && un_acked[0].arrow_Message_seqno()
        <= seqno_acked {
        truncate_un_ack_list(un_acked.skip(1), seqno_acked)
    } else {
        un_acked
    }
}

#[verifier::ext_equal]
pub struct AckState<MT> {
    pub num_packets_acked: nat,
    pub un_acked: AckList<MT>,
}

pub open spec(checked) fn ack_state_lookup<MT>(
    src: AbstractEndPoint,
    send_state: SendState<MT>,
) -> AckState<MT> {
    if send_state.contains_key(src) {
        send_state[src]
    } else {
        AckState { num_packets_acked: 0, un_acked: Seq::empty() }
    }
}

#[verifier::ext_equal]
pub struct SingleDelivery<MT> {
    pub receive_state: TombstoneTable,
    pub send_state: SendState<MT>,
}

impl<MT> SingleDelivery<MT> {
    pub open spec(checked) fn new_single_message(self, pkt: Packet) -> bool {
        let last_seqno = tombstone_table_lookup(pkt.src, self.receive_state);
        &&& pkt.msg is Message
        &&& pkt.msg.arrow_Message_seqno() == last_seqno + 1
    }

    pub open spec(checked) fn receive_ack(
        pre: Self,
        post: Self,
        pkt: Packet,
        acks: Set<Packet>,
    ) -> bool
        recommends
            pkt.msg is Ack,
    {
        &&& acks.is_empty()
        &&& {
            let old_ack_state = ack_state_lookup(pkt.src, pre.send_state);
            if pkt.msg.arrow_Ack_ack_seqno() > old_ack_state.num_packets_acked {
                let new_ack_state = AckState {
                    num_packets_acked: pkt.msg.arrow_Ack_ack_seqno(),
                    un_acked: truncate_un_ack_list(
                        old_ack_state.un_acked,
                        pkt.msg.arrow_Ack_ack_seqno(),
                    ),
                    ..old_ack_state
                };
                post =~= Self { send_state: pre.send_state.insert(pkt.src, new_ack_state), ..post }
            } else {
                post == pre
            }
        }
    }

    pub open spec(checked) fn receive_real_packet(self, post: Self, pkt: Packet) -> bool {
        if self.new_single_message(pkt) {
            let last_seqno = tombstone_table_lookup(pkt.src, self.receive_state);
            post == Self {
                receive_state: self.receive_state.insert(pkt.src, (last_seqno + 1) as nat),
                ..self
            }
        } else {
            post == self
        }
    }

    pub open spec(checked) fn should_ack_single_message(self, pkt: Packet) -> bool {
        &&& pkt.msg is Message
        &&& {
            let last_seqno = tombstone_table_lookup(pkt.src, self.receive_state);
            pkt.msg.arrow_Message_seqno() <= last_seqno
        }
    }

    pub open spec(checked) fn send_ack(self, pkt: Packet, ack: Packet, acks: Set<Packet>) -> bool
        recommends
            self.should_ack_single_message(pkt),
    {
        &&& ack.msg is Ack
        &&& ack.msg.arrow_Ack_ack_seqno() == pkt.msg.arrow_Message_seqno()
        &&& ack.src == pkt.dst
        &&& ack.dst == pkt.src
        &&& acks == set![ack]
    }

    pub open spec(checked) fn maybe_ack_packet(
        pre: Self,
        pkt: Packet,
        ack: Packet,
        acks: Set<Packet>,
    ) -> bool {
        if pre.should_ack_single_message(pkt) {
            pre.send_ack(pkt, ack, acks)
        } else {
            acks.is_empty()
        }
    }

    pub open spec(checked) fn receive(
        pre: Self,
        post: Self,
        pkt: Packet,
        ack: Packet,
        acks: Set<Packet>,
    ) -> bool {
        match pkt.msg {
            SingleMessage::Ack { ack_seqno: _ } => Self::receive_ack(pre, post, pkt, acks),
            SingleMessage::Message { seqno, dst: _, m } => {
                &&& Self::receive_real_packet(pre, post, pkt)
                &&& Self::maybe_ack_packet(post, pkt, ack, acks)
            },
            SingleMessage::InvalidMessage {  } => {
                &&& post === pre
                &&& acks === Set::empty()
            },
        }
    }

    pub open spec(checked) fn send_single_message(
        pre: Self,
        post: Self,
        m: MT,
        dst: AbstractEndPoint,
        sm: Option<SingleMessage<MT>>,
        params: AbstractParameters,
    ) -> bool {
        let old_ack_state = ack_state_lookup(dst, pre.send_state);
        let new_seqno = old_ack_state.num_packets_acked + old_ack_state.un_acked.len() + 1;
        if new_seqno > params.max_seqno {
            &&& post == pre
            &&& sm is None
        } else {
            &&& sm == Some(SingleMessage::<MT>::Message { seqno: new_seqno, m: m, dst: dst })
            &&& post == SingleDelivery {
                send_state: pre.send_state.insert(
                    dst,
                    AckState {
                        un_acked: old_ack_state.un_acked.push(sm.unwrap()),
                        ..old_ack_state
                    },
                ),
                ..pre
            }
        }
    }

    pub open spec(checked) fn receive_no_message(pre: Self, post: Self) -> bool {
        post.receive_state == pre.receive_state
    }

    pub open spec(checked) fn send_no_message(pre: Self, post: Self) -> bool {
        post.send_state == pre.send_state
    }
}

impl SingleDelivery<Message> {
    pub open spec(checked) fn un_acked_messages_for_dest_up_to(
        self,
        src: AbstractEndPoint,
        dst: AbstractEndPoint,
        count: nat,
    ) -> Set<Packet>
        recommends
            self.send_state.contains_key(dst),
            count <= self.send_state[dst].un_acked.len(),
    {
        Set::new(
            |p: Packet|
                {
                    &&& p.src == src
                    &&& exists|i: int|
                        {
                            &&& 0 <= i < count
                            &&& self.send_state[dst].un_acked[i] is Message
                            &&& p.msg == self.send_state[dst].un_acked[i]
                            &&& p.dst == p.msg.arrow_Message_dst()
                        }
                },
        )
    }

    pub open spec(checked) fn un_acked_messages_for_dest(
        self,
        src: AbstractEndPoint,
        dst: AbstractEndPoint,
    ) -> Set<Packet>
        recommends
            self.send_state.contains_key(dst),
    {
        self.un_acked_messages_for_dest_up_to(src, dst, self.send_state[dst].un_acked.len())
    }

    pub open spec fn un_acked_messages_for_dests(
        self,
        src: AbstractEndPoint,
        dsts: Set<AbstractEndPoint>,
    ) -> Set<Packet>
        recommends
            dsts.subset_of(self.send_state.dom()),
    {
        flatten_sets(dsts.map(|dst: AbstractEndPoint| self.un_acked_messages_for_dest(src, dst)))
    }

    pub open spec fn un_acked_messages(self, src: AbstractEndPoint) -> Set<Packet> {
        self.un_acked_messages_for_dests(src, self.send_state.dom())
    }
}

pub enum SingleMessage<MT> {
    Message { seqno: nat, dst: AbstractEndPoint, m: MT },
    Ack { ack_seqno: nat },
    InvalidMessage {  },
}

pub open spec fn flatten_sets<A>(sets: Set<Set<A>>) -> Set<A> {
    Set::new(|a: A| (exists|s: Set<A>| sets.contains(s) && s.contains(a)))
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

#[verifier::opaque]
pub open spec fn seq_is_unique<T>(s: Seq<T>) -> bool {
    forall|i: int, j: int|
        #![trigger s[i], s[j]]
        0 <= i && i < s.len() && 0 <= j && j < s.len() && s[i] == s[j] ==> i == j
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

pub open spec fn extract_range(h: Hashtable, kr: KeyRange<AbstractKey>) -> Hashtable {
    Map::<AbstractKey, AbstractValue>::new(
        |k: AbstractKey| h.dom().contains(k) && kr.contains(k),
        |k: AbstractKey| h[k],
    )
}

pub trait VerusClone {

}

impl VerusClone for SHTKey {

}

pub type AbstractKey = SHTKey;

pub type CKey = SHTKey;

pub type Hashtable = Map<AbstractKey, AbstractValue>;

pub type AbstractValue = Seq<u8>;

type ID = EndPoint;

#[verifier::reject_recursive_types(K)]
struct StrictlyOrderedMap<K: KeyTrait + VerusClone> {
    keys: StrictlyOrderedVec<K>,
    vals: Vec<ID>,
    m: Ghost<Map<K, ID>>,
}

struct StrictlyOrderedVec<K: KeyTrait> {
    v: Vec<K>,
}

pub type Arg = Vec<u8>;

pub type Args = Vec<Arg>;

pub type AbstractArg = Seq<u8>;

pub type AbstractArgs = Seq<AbstractArg>;

define_enum_and_derive_marshalable! { pub enum CSingleMessage { #[tag = 0] Message {
    #[o = o0] seqno : u64, #[o = o1] dst : EndPoint, #[o = o2] m : CMessage }, #[tag = 1]
    Ack { #[o = o0] ack_seqno : u64 }, #[tag = 2] InvalidMessage, } [rlimit attr =
    verifier::rlimit(25)] }

pub type LSHTPacket = LPacket<AbstractEndPoint, SingleMessage<Message>>;

pub type AckList<MT> = Seq<SingleMessage<MT>>;

pub type PMsg = SingleMessage<Message>;

pub type SendState<MT> = Map<AbstractEndPoint, AckState<MT>>;

pub type TombstoneTable = Map<AbstractEndPoint, nat>;

marshalable_by_bijection! { [EndPoint] <-> [Vec::< u8 >];
    forward(self) self.id; backward(x) EndPoint { id : x }; }

derive_marshalable_for_enum! { pub enum CMessage { #[tag = 0] GetRequest { #[o = o0]
    k : CKey }, #[tag = 1] SetRequest { #[o = o0] k : CKey, #[o = o1] v : Option::< Vec <
    u8 >> }, #[tag = 2] Reply { #[o = o0] k : CKey, #[o = o1] v : Option::< Vec::< u8 >>
    }, #[tag = 3] Redirect { #[o = o0] k : CKey, #[o = o1] id : EndPoint }, #[tag = 4]
    Shard { #[o = o0] kr : KeyRange::< CKey >, #[o = o1] recipient : EndPoint }, #[tag =
    5] Delegate { #[o = o0] range : KeyRange::< CKey >, #[o = o1] h : CKeyHashMap }, }
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

pub type NetEvent = LIoOp<AbstractEndPoint, Seq<u8>>;

pub type NetPacket = LPacket<AbstractEndPoint, Seq<u8>>;

pub type History = Seq<NetEvent>;

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

type Ios = Seq<NetEvent>;

impl HostState {
    pub closed spec fn view(self) -> AbstractHostState {
        AbstractHostState {
            constants: self.constants@,
            delegation_map: AbstractDelegationMap(self.delegation_map@),
            h: self.h@,
            sd: self.sd@,
            received_packet: match self.received_packet {
                None => None,
                Some(cpacket) => Some(cpacket@),
            },
            num_delegations: self.num_delegations as int,
            received_requests: self.received_requests@,
        }
    }

    pub closed spec fn abstractable(&self) -> bool {
        self.constants.abstractable()
    }

    pub closed spec fn valid(&self) -> bool {
        &&& self.abstractable()
        &&& self.delegation_map.valid()
        &&& (forall|k| self.h@.dom().contains(k) ==> #[trigger] valid_value(self.h@[k]))
        &&& self.sd.valid()
        &&& match &self.received_packet {
            Some(v) => v.abstractable() && v.msg is Message && v.dst@ == self.constants.me@,
            None => true,
        }
        &&& self.constants.valid()
        &&& self.num_delegations < self.constants.params.max_delegations
    }

    pub closed spec fn invariants(&self, netc_end_point: &AbstractEndPoint) -> bool {
        &&& self.next_action_index < 3
        &&& self.delegation_map.valid()
        &&& self@.constants.me == netc_end_point
        &&& self.valid()
        &&& self@.constants.me.abstractable()
        &&& self.num_delegations < self.constants.params.max_delegations
        &&& self.constants.params@ == AbstractParameters::static_params()
        &&& self.resend_count < 100000000
    }

    #[verifier::external_body]
    #[verifier(spinoff_prover)]
    fn host_next_receive_packet(
        &mut self,
        netc: &mut NetClient,
        Ghost(old_netc_history): Ghost<Seq<NetEvent>>,
        cpacket: CPacket,
        Ghost(receive_event): Ghost<NetEvent>,
    ) -> (rc: (bool, Ghost<EventResults>, Ghost<Seq<LSHTIo>>))
        requires
            old(netc).ok(),
            old(self).invariants(&old(netc).my_end_point()),
            !(cpacket.msg is InvalidMessage),
            cpacket.dst@ == old(self).constants.me@,
            cpacket.abstractable(),
            cpacket.src@.valid_physical_address(),
            old(netc).history() == old_netc_history.push(receive_event),
            receive_event is Receive,
            abstractify_cpacket_to_lsht_packet(cpacket) == abstractify_net_packet_to_lsht_packet(
                receive_event.arrow_Receive_r(),
            ),
        ensures
            ({
                let (ok, Ghost(event_results), Ghost(ios)) = rc;
                &&& self.invariants(&netc.my_end_point())
                &&& self@.constants == old(self)@.constants
                &&& ok == netc.ok()
                &&& (ok || event_results.sends.len() > 0) ==> netc.history() == old_netc_history
                    + event_results.ios
                &&& event_results.ios == event_results.event_seq()
                &&& event_results.well_typed_events()
                &&& ok ==> {
                    &&& receive_packet_next(old(self)@, self@, ios)
                    &&& raw_io_consistent_with_spec_io(event_results.ios, ios)
                    &&& no_invalid_sends(ios)
                }
            }),
    {
        unimplemented!()
    }

    pub fn receive_packet_next(&mut self, netc: &mut NetClient) -> (rc: (bool, Ghost<EventResults>))
        requires
            Self::next_requires(*old(self), *old(netc)),
        ensures
            Self::next_ensures(*old(self), *old(netc), *self, *netc, rc),
    {
        let (rr, Ghost(ret_receive_with_demarshal_ghost0)) = receive_with_demarshal(netc, &self.constants.me);
        match rr {
            ReceiveResult::Fail {  } => {
                let ghost ret_ghost0: EventResults = arbitrary(); // TODO - replace with correct value
                let ret = (
                    false,
                    Ghost(ret_ghost0),
                );
                return ret;
            },
            ReceiveResult::Timeout {  } => {
                let iop: NetEvent = LIoOp::TimeoutReceive {  };
                let ghost ret_ghost0: EventResults = arbitrary(); // TODO - replace with correct value
                let ret = (true, Ghost(ret_ghost0));
                return ret;
            },
            ReceiveResult::Packet { cpacket } => {
                match cpacket.msg {
                    CSingleMessage::InvalidMessage {  } => {
                        let ghost ret_ghost0: EventResults = arbitrary(); // TODO - replace with correct value
                        let ret = (true, Ghost(ret_ghost0));
                        return ret;
                    },
                    _ => {
                        let ghost host_next_receive_packet_ghost0: Seq<NetEvent> = arbitrary(); // TODO - replace with correct value
                        let ghost host_next_receive_packet_ghost1: NetEvent = arbitrary(); // TODO - replace with correct value
                        let (ok, Ghost(ret_host_next_receive_packet_ghost0), Ghost(ret_host_next_receive_packet_ghost1)) = self.host_next_receive_packet(
                            netc,
                            Ghost(host_next_receive_packet_ghost0),
                            cpacket,
                            Ghost(host_next_receive_packet_ghost1),
                        );
                        if !ok {
                            let ghost ret_ghost0: EventResults = arbitrary(); // TODO - replace with correct value
                            let ret = (ok, Ghost(ret_ghost0));
                            return ret;
                        }
                        let ghost ret_ghost0: EventResults = arbitrary(); // TODO - replace with correct value
                        let rc = (ok, Ghost(ret_ghost0));
                        rc
                    },
                }
            },
        }
    }
}

} // verus!
