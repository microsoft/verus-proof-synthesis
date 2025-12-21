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

    pub open spec fn message_marshallable(&self) -> bool {
        match self {
            CMessage::GetRequest { k } => valid_key(*k),
            CMessage::SetRequest { k, v } => valid_key(*k) && valid_optional_value(
                optional_value_view(*v),
            ),
            CMessage::Reply { k, v } => valid_key(*k) && valid_optional_value(
                optional_value_view(*v),
            ),
            CMessage::Redirect { k, id } => valid_key(*k) && id@.valid_physical_address(),
            CMessage::Shard { kr, recipient } => recipient@.valid_physical_address()
                && !kr.is_empty(),
            CMessage::Delegate { range, h } => !range.is_empty() && valid_hashtable(h@),
        }
    }

    #[verifier::external_body]
    pub fn is_message_marshallable(&self) -> (b: bool)
        ensures
            b == self.message_marshallable(),
    {
        unimplemented!()
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

pub open spec fn cpacket_seq_is_abstractable(packets: Seq<CPacket>) -> bool {
    forall|i: int| 0 <= i && i < packets.len() ==> #[trigger] packets[i].abstractable()
}

pub open spec fn abstractify_outbound_packets_to_seq_of_lsht_packets(packets: Seq<CPacket>) -> Seq<
    LSHTPacket,
>
    recommends
        cpacket_seq_is_abstractable(packets),
{
    packets.map_values(|packet: CPacket| abstractify_cpacket_to_lsht_packet(packet))
}

pub open spec fn abstractify_seq_of_cpackets_to_set_of_sht_packets(cps: Seq<CPacket>) -> Set<Packet>
    recommends
        cpacket_seq_is_abstractable(cps),
{
    cps.map_values(|cp: CPacket| cp@).to_set()
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

#[allow(unused_macros)] macro_rules! derive_marshalable_for_struct { { $(#[$attr :
    meta])* $pub : vis struct $newstruct : ident $(< $($poly : ident : Marshalable),+
    $(,)? >)? { $($fieldvis : vis $field : ident : $fieldty : ty),+ $(,)? } } => {
    ::builtin_macros::verus! { impl $(< $($poly : Marshalable),* >)? Marshalable for
    $newstruct $(< $($poly),* >)? { open spec fn is_marshalable(& self) -> bool { $(&&&
    self.$field .is_marshalable())* &&& 0 $(+ self.$field .ghost_serialize().len())* <=
    usize::MAX } open spec fn ghost_serialize(& self) -> Seq < u8 > { Seq::empty() $(+
    self.$field .ghost_serialize())* } } } } }

macro_rules! derive_marshalable_for_enum {
    { $(#[$attr : meta])* $pub : vis enum $newenum : ident $(< $($poly : ident :
    Marshalable),+ $(,)? >)? { $(#[tag = $tag : literal] $variant : ident $({ $(#[o
    =$memother : ident] $member : ident : $memberty : ty),* $(,)? })?),+ $(,)? }
    $([rlimit attr = $rlimitattr : meta])? } => { ::builtin_macros::verus! { impl $(<
    $($poly : Marshalable),+ >)? Marshalable for $newenum $(< $($poly),+ >)? { open spec
    fn is_marshalable(& self) -> bool { &&& match self { $($newenum ::$variant $({
    $($member),* })? => { $($(&&& $member .is_marshalable())*)? &&& 1 $($(+ $member
    .ghost_serialize().len())*)? <= usize::MAX }),+ } } open spec fn ghost_serialize(&
    self) -> Seq < u8 > { match self { $($newenum ::$variant $({ $($member),* })? => {
    seq![$tag] $($(+ $member .ghost_serialize())*)? }),* } } } } } }

#[allow(unused_macros)] macro_rules! define_enum_and_derive_marshalable { { $(#[$attr
    : meta])* $pub : vis enum $newenum : ident $(< $($poly : ident : Marshalable),+ $(,)?
    >)? { $(#[tag = $tag : literal] $variant : ident $({ $(#[o =$memother : ident]
    $member : ident : $memberty : ty),* $(,)? })?),+ $(,)? } $([rlimit attr = $rlimitattr
    : meta])? } => { ::builtin_macros::verus! { $(#[$attr])* $pub enum $newenum $(<
    $($poly : Marshalable),+ >)? { $($variant $({ $($member : $memberty),* })?),+ } }
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
    pub open spec fn is_end_spec(&self) -> bool {
        self.k.is_None()
    }

    pub open spec fn get_spec(&self) -> &K
        recommends
            self.k.is_some(),
    {
        &self.k.get_Some_0()
    }

    #[verifier::external_body]
    #[verifier(when_used_as_spec(get_spec))]
    pub fn get(&self) -> (k: &K) {
        unimplemented!()
    }

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

    #[verifier::external_body]
    pub proof fn valid_implies_complete(&self)
        requires
            self.valid(),
        ensures
            self@.dom().is_full(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub fn set(&mut self, lo: &KeyIterator<K>, hi: &KeyIterator<K>, dst: &ID)
        requires
            old(self).valid(),
            dst@.valid_physical_address(),
        ensures
            self.valid(),
            forall|ki: KeyIterator<K>| #[trigger]
                KeyIterator::between(*lo, ki, *hi) ==> self@[*ki.get()] == dst@,
            forall|ki: KeyIterator<K>|
                !ki.is_end_spec() && !(#[trigger] KeyIterator::between(*lo, ki, *hi))
                    ==> self@[*ki.get()] == old(self)@[*ki.get()],
    {
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

    pub open spec fn is_complete(self) -> bool {
        self@.dom().is_full()
    }

    pub open spec fn update(self, newkr: KeyRange<AbstractKey>, host: AbstractEndPoint) -> Self
        recommends
            self.is_complete(),
    {
        AbstractDelegationMap(self@.union_prefer_right(Map::new(|k| newkr.contains(k), |k| host)))
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

#[verifier(external_body)]
pub struct CKeyHashMap {
    m: collections::HashMap<CKey, Vec<u8>>,
}

impl CKeyHashMap {
    pub uninterp spec fn view(self) -> Map<AbstractKey, Seq<u8>>;

    #[verifier::external_body]
    #[verifier(external_body)]
    pub fn bulk_update(&mut self, kr: &KeyRange::<CKey>, other: &Self)
        ensures
            self@ == Map::<AbstractKey, Seq<u8>>::new(
                |k: AbstractKey|
                    (old(self)@.dom().contains(k) || other@.dom().contains(k)) && (kr.contains(k)
                        ==> other@.dom().contains(k)),
                |k: AbstractKey|
                    if other@.dom().contains(k) {
                        other@[k]
                    } else {
                        old(self)@[k]
                    },
            ),
    {
        unimplemented!()
    }

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

pub open spec fn max_hashtable_size() -> int {
    62
}

pub open spec fn valid_hashtable(h: Hashtable) -> bool {
    &&& h.dom().len() < max_hashtable_size()
    &&& (forall|k| h.dom().contains(k) ==> valid_key(k) && #[trigger] valid_value(h[k]))
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

pub open spec(checked) fn valid_optional_value(ov: Option<AbstractValue>) -> bool {
    match ov {
        None => true,
        Some(value) => valid_value(value),
    }
}

pub open spec fn extract_packet_from_lsht_packet(lp: LSHTPacket) -> Packet {
    Packet { dst: lp.dst, src: lp.src, msg: lp.msg }
}

pub open spec fn extract_packets_from_lsht_packets(seq_packets: Seq<LSHTPacket>) -> Set<Packet> {
    seq_packets.map_values(|lp: LSHTPacket| extract_packet_from_lsht_packet(lp)).to_set()
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

#[derive(Eq, PartialEq, Hash)]
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

impl<MT> SingleDelivery<MT> {
    pub open spec(checked) fn receive_no_message(pre: Self, post: Self) -> bool {
        post.receive_state == pre.receive_state
    }

    pub open spec(checked) fn send_no_message(pre: Self, post: Self) -> bool {
        post.send_state == pre.send_state
    }
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

#[verifier::opaque]
pub open spec fn seq_is_unique<T>(s: Seq<T>) -> bool {
    forall|i: int, j: int|
        #![trigger s[i], s[j]]
        0 <= i && i < s.len() && 0 <= j && j < s.len() && s[i] == s[j] ==> i == j
}

#[verifier::external_body]
pub fn endpoints_contain(endpoints: &Vec<EndPoint>, endpoint: &EndPoint) -> (present: bool)
    ensures
        present == abstractify_end_points(*endpoints).contains(endpoint@),
{
    unimplemented!()
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

    pub closed spec fn host_ignoring_unparseable(
        pre: AbstractHostState,
        post: AbstractHostState,
        packets: Set<Packet>,
    ) -> bool {
        &&& packets.len() == 0
        &&& post == AbstractHostState { received_packet: None, ..pre }
        &&& pre.received_packet is Some
        &&& pre.received_packet.arrow_Some_0().msg is Message
        &&& match pre.received_packet.arrow_Some_0().msg.arrow_Message_m() {
            Message::Delegate { range: range, h: h } => !({
                &&& valid_hashtable(h)
                &&& !range.is_empty()
                &&& pre.received_packet.arrow_Some_0().msg.arrow_Message_dst().valid_physical_address()
            }),
            _ => false,
        }
    }

    pub closed spec fn host_state_packet_preconditions(&self, cpacket: CPacket) -> bool {
        &&& self.abstractable()
        &&& cpacket.abstractable()
        &&& self.valid()
        &&& cpacket.src@.valid_physical_address()
        &&& self.constants.params@ == AbstractParameters::static_params()
        &&& self.resend_count < 100000000
    }

    pub closed spec fn host_state_common_preconditions(&self) -> bool {
        match self.received_packet {
            Some(cpacket) => self.host_state_packet_preconditions(cpacket),
            None => false,
        }
    }

    pub closed spec fn next_delegate_preconditions(&self) -> bool {
        &&& self.abstractable()
        &&& {
            let cpacket = self.received_packet.unwrap();
            {
                &&& cpacket.abstractable()
                &&& cpacket.msg is Message
                &&& cpacket.msg.arrow_Message_m() is Delegate
                &&& cpacket.src@.valid_physical_address()
            }
        }
        &&& self.sd.valid()
        &&& self.host_state_common_preconditions()
        &&& self.constants.me@.valid_physical_address()
        &&& self.sd.valid()
        &&& self.num_delegations < self.constants.params.max_delegations - 2
    }

    pub closed spec fn next_delegate_postconditions(
        &self,
        pre: Self,
        sent_packets: Seq<CPacket>,
    ) -> bool {
        &&& pre.next_delegate_preconditions()
        &&& self.abstractable()
        &&& cpacket_seq_is_abstractable(sent_packets)
        &&& self.host_state_common_postconditions(pre, pre.received_packet.unwrap(), sent_packets)
        &&& self.received_packet is None
        &&& {
            ||| next_delegate(
                pre@,
                self@,
                pre.received_packet.unwrap()@,
                abstractify_seq_of_cpackets_to_set_of_sht_packets(sent_packets),
            )
            ||| Self::host_ignoring_unparseable(
                pre@,
                self@,
                abstractify_seq_of_cpackets_to_set_of_sht_packets(sent_packets),
            )
        }
    }

    pub closed spec fn host_state_common_postconditions(
        &self,
        pre: Self,
        cpacket: CPacket,
        sent_packets: Seq<CPacket>,
    ) -> bool {
        &&& self.abstractable()
        &&& self.constants == pre.constants
        &&& cpacket_seq_is_abstractable(sent_packets)
        &&& self.valid()
        &&& self.next_action_index == pre.next_action_index
        &&& outbound_packet_seq_is_valid(sent_packets)
        &&& outbound_packet_seq_has_correct_srcs(sent_packets, pre.constants.me@)
        &&& (forall|i: int|
            0 <= i && i < sent_packets.len() ==> (#[trigger] sent_packets[i].msg) is Message
                || sent_packets[i].msg is Ack)
        &&& abstractify_seq_of_cpackets_to_set_of_sht_packets(sent_packets)
            =~= extract_packets_from_lsht_packets(
            abstractify_outbound_packets_to_seq_of_lsht_packets(sent_packets),
        )
        &&& self.resend_count < 100000000
    }

    #[verifier::external_body]
    proof fn effect_of_delegation_map_set(
        pre: DelegationMap<CKey>,
        post: DelegationMap<CKey>,
        lo: &KeyIterator<CKey>,
        hi: &KeyIterator<CKey>,
        dst: &EndPoint,
    )
        requires
            pre.valid(),
            post.valid(),
            forall|ki: KeyIterator<CKey>| #[trigger]
                KeyIterator::between(*lo, ki, *hi) ==> post@[*ki.get()] == dst@,
            forall|ki: KeyIterator<CKey>|
                !ki.is_end_spec() && !(#[trigger] KeyIterator::between(*lo, ki, *hi))
                    ==> post@[*ki.get()] == pre@[*ki.get()],
        ensures
            AbstractDelegationMap(post@) == AbstractDelegationMap(pre@).update(
                KeyRange::<AbstractKey> { lo: *lo, hi: *hi },
                dst@,
            ),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    proof fn effect_of_hashmap_bulk_update(
        pre: CKeyHashMap,
        post: CKeyHashMap,
        kr: &KeyRange::<CKey>,
        other: CKeyHashMap,
    )
        requires
            forall|k| pre@.dom().contains(k) ==> #[trigger] valid_value(pre@[k]),
            valid_hashtable(other@),
            post@ == Map::<AbstractKey, Seq<u8>>::new(
                |k: AbstractKey|
                    (pre@.dom().contains(k) || other@.dom().contains(k)) && (kr.contains(k)
                        ==> other@.dom().contains(k)),
                |k: AbstractKey|
                    if other@.dom().contains(k) {
                        other@[k]
                    } else {
                        pre@[k]
                    },
            ),
        ensures
            post@ == bulk_update_hashtable(pre@, *kr, other@),
            forall|k| post@.dom().contains(k) ==> #[trigger] valid_value(post@[k]),
    {
        unimplemented!()
    }

    fn host_model_next_delegate(&mut self) -> (sent_packets: Vec<CPacket>)
        requires
            old(self).next_delegate_preconditions(),
        ensures
            self.next_delegate_postconditions(*old(self), sent_packets@),
    {
        let sent_packets = vec![];
        let cpacket: &CPacket = &self.received_packet.as_ref().unwrap();
        match &cpacket.msg {
            CSingleMessage::Message { m, seqno, .. } => {
                match m {
                    CMessage::Delegate { range, h } => {
                        let marshalable: bool = m.is_message_marshallable();
                        if (!marshalable) {
                            self.received_packet = None;
                            return sent_packets;
                        } else if !endpoints_contain(&self.constants.host_ids, &cpacket.src) {
                            self.received_packet = None;
                            return sent_packets;
                        } else {
                            self.delegation_map.set(&range.lo, &range.hi, &self.constants.me);
                            self.h.bulk_update(&range, &h);
                            self.received_packet = None;
                            self.num_delegations = self.num_delegations + 1;
                            return sent_packets;
                        }
                    },
                    _ => { unreached() },
                }
            },
            _ => { unreached() },
        };
        unreached()
    }
}

} // verus!
