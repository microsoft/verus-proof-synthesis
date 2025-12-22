extern crate verus_builtin_macros as builtin_macros;
use std::collections;
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

    #[verifier::external_body]
    pub fn clone_up_to_view(&self) -> (c: Self)
        ensures
            c@ == self@,
    {
        unimplemented!()
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

#[verifier::external_body]
pub proof fn same_view_same_marshalable(x: &CSingleMessage, y: &CSingleMessage)
    requires
        x@ == y@,
    ensures
        x.is_marshalable() == y.is_marshalable(),
{
    unimplemented!()
}

pub enum ReceiveImplResult {
    FreshPacket { ack: CPacket },
    DuplicatePacket { ack: CPacket },
    AckOrInvalid,
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

    #[verifier::external_body]
    pub proof fn un_acked_messages_extend(
        &self,
        src: AbstractEndPoint,
        dst: AbstractEndPoint,
        i: nat,
    )
        requires
            self@.send_state.contains_key(dst),
            i < self@.send_state[dst].un_acked.len(),
            self.send_state.valid(),
        ensures
            self@.un_acked_messages_for_dest_up_to(src, dst, i + 1)
                == self@.un_acked_messages_for_dest_up_to(src, dst, i).insert(
                Packet { src, dst, msg: self@.send_state[dst].un_acked[i as int] },
            ),
    {
        unimplemented!()
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

    pub open spec fn get_spec(map_v: Map<AbstractEndPoint, V>, key: AbstractEndPoint) -> (value:
        Option<V>) {
        if map_v.dom().contains(key) {
            Some(map_v[key])
        } else {
            None
        }
    }

    #[verifier::external_body]
    #[verifier(external_body)]
    pub fn get<'a>(&'a self, key: &EndPoint) -> (value: Option<&'a V>)
        ensures
            value == match Self::get_spec(self@, key@) {
                Some(v) => Some(&v),
                None => None,
            },
    {
        unimplemented!()
    }
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
    #[verifier::external_body]
    pub fn clone_up_to_view(&self) -> (res: EndPoint)
        ensures
            res@ == self@,
    {
        unimplemented!()
    }

    pub open spec fn view(self) -> AbstractEndPoint {
        AbstractEndPoint { id: self.id@ }
    }

    #[verifier(inline)]
    pub open spec fn abstractable(self) -> bool {
        self@.valid_physical_address()
    }
}

pub struct KeyIterator<K: KeyTrait + VerusClone> {
    pub k: Option<K>,
}

pub struct KeyRange<K: KeyTrait + VerusClone> {
    pub lo: KeyIterator<K>,
    pub hi: KeyIterator<K>,
}

#[derive(Eq, PartialEq, Hash)]
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

#[verifier::ext_equal]
pub struct AckState<MT> {
    pub num_packets_acked: nat,
    pub un_acked: AckList<MT>,
}

#[verifier::ext_equal]
pub struct SingleDelivery<MT> {
    pub receive_state: TombstoneTable,
    pub send_state: SendState<MT>,
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
}

pub enum SingleMessage<MT> {
    Message { seqno: nat, dst: AbstractEndPoint, m: MT },
    Ack { ack_seqno: nat },
    InvalidMessage {  },
}

#[verifier::external_body]
pub proof fn lemma_seq_push_to_set<A>(s: Seq<A>, x: A)
    ensures
        s.push(x).to_set() == s.to_set().insert(x),
{
    unimplemented!()
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

pub open spec fn outbound_packet_is_valid(cpacket: &CPacket) -> bool {
    &&& cpacket.abstractable()
    &&& cpacket.msg.is_marshalable()
    &&& !(cpacket.msg is InvalidMessage)
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

pub trait KeyTrait {

}

pub trait VerusClone {

}

impl VerusClone for SHTKey {

}

impl KeyTrait for SHTKey {

}

define_enum_and_derive_marshalable! { pub enum CSingleMessage { #[tag = 0] Message {
    #[o = o0] seqno : u64, #[o = o1] dst : EndPoint, #[o = o2] m : CMessage }, #[tag = 1]
    Ack { #[o = o0] ack_seqno : u64 }, #[tag = 2] InvalidMessage, } [rlimit attr =
    verifier::rlimit(25)] }

pub type AbstractKey = SHTKey;

pub type CKey = SHTKey;

pub type Hashtable = Map<AbstractKey, AbstractValue>;

pub type AbstractValue = Seq<u8>;

type ID = EndPoint;

derive_marshalable_for_enum! { pub enum CMessage { #[tag =
    0] GetRequest { #[o = o0] k : CKey }, #[tag = 1] SetRequest { #[o = o0] k : CKey, #[o
    = o1] v : Option::< Vec < u8 >> }, #[tag = 2] Reply { #[o = o0] k : CKey, #[o = o1] v
    : Option::< Vec::< u8 >> }, #[tag = 3] Redirect { #[o = o0] k : CKey, #[o = o1] id :
    EndPoint }, #[tag = 4] Shard { #[o = o0] kr : KeyRange::< CKey >, #[o = o1] recipient
    : EndPoint }, #[tag = 5] Delegate { #[o = o0] range : KeyRange::< CKey >, #[o = o1] h
    : CKeyHashMap }, } [rlimit attr = verifier::rlimit(20)] }

marshalable_by_bijection! {
    [KeyRange::< CKey >] <-> [(Option::< u64 >, Option::< u64 >)]; forward(self) { (match
    & self.lo.k { None => None, Some(x) => Some(x.ukey), }, match & self.hi.k { None =>
    None, Some(x) => Some(x.ukey), },) }; backward(x) { KeyRange { lo : KeyIterator { k :
    match x.0 { None => None, Some(x) => Some(SHTKey { ukey : x }), } }, hi : KeyIterator
    { k : match x.1 { None => None, Some(x) => Some(SHTKey { ukey : x }), } }, } }; }

marshalable_by_bijection! { [EndPoint] <-> [Vec::< u8 >]; forward(self) self.id;
    backward(x) EndPoint { id : x }; }

marshalable_by_bijection! { [SHTKey] <-> [u64];
    forward(self) self.ukey; backward(x) SHTKey { ukey : x }; }

derive_marshalable_for_struct! { pub struct CKeyKV { pub k : CKey, pub v : Vec::< u8
    >, } }

pub type AckList<MT> = Seq<SingleMessage<MT>>;

pub type TombstoneTable = Map<AbstractEndPoint, nat>;

pub type SendState<MT> = Map<AbstractEndPoint, AckState<MT>>;

pub type PMsg = SingleMessage<Message>;

impl CSingleDelivery {
    pub open spec fn packets_are_valid_messages(packets: Seq<CPacket>) -> bool {
        forall|i| 0 <= i < packets.len() ==> #[trigger] packets[i].msg is Message
    }

    pub fn retransmit_un_acked_packets_for_dst(
        &self,
        src: &EndPoint,
        dst: &EndPoint,
        packets: &mut Vec<CPacket>,
    )
        requires
            self.valid(),
            src.abstractable(),
            outbound_packet_seq_is_valid(old(packets)@),
            outbound_packet_seq_has_correct_srcs(old(packets)@, src@),
            self.send_state@.contains_key(dst@),
            Self::packets_are_valid_messages(old(packets)@),
        ensures
            packets@.map_values(|p: CPacket| p@).to_set() == old(packets)@.map_values(
                |p: CPacket| p@,
            ).to_set() + self@.un_acked_messages_for_dest(src@, dst@),
            outbound_packet_seq_is_valid(packets@),
            outbound_packet_seq_has_correct_srcs(packets@, src@),
            Self::packets_are_valid_messages(packets@),
    {
        match self.send_state.epmap.get(dst) {
            Some(ack_state) => {
                let mut i = 0;
                while i < ack_state.un_acked.len() {
                    let sm = &ack_state.un_acked[i];
                    let dst = match sm {
                        CSingleMessage::Message { dst, .. } => dst,
                        _ => { unreached() },
                    };
                    let cpacket = CPacket {
                        dst: dst.clone_up_to_view(),
                        src: src.clone_up_to_view(),
                        msg: sm.clone_up_to_view(),
                    };
                    packets.push(cpacket);
                    i = i + 1;
                }
            },
            None => {},
        }
    }
}

} // verus!
