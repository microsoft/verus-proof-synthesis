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

    #[verifier::external_body]
    pub fn clone_up_to_view(&self) -> (c: Self)
        ensures
            c@ == self@,
    {
        unimplemented!()
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

pub trait Marshalable: Sized {
    spec fn is_marshalable(&self) -> bool;

    #[verifier::external_body]
    spec fn ghost_serialize(&self) -> Seq<u8>
        recommends
            self.is_marshalable(),
    {
        unimplemented!()
    }

    spec fn view_equal(&self, other: &Self) -> bool;

    #[verifier::external_body]
    proof fn lemma_same_views_serialize_the_same(&self, other: &Self)
        requires
            self.view_equal(other),
        ensures
            self.is_marshalable() == other.is_marshalable(),
            self.ghost_serialize() == other.ghost_serialize(),
    {
        unimplemented!()
    }
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
}

impl Marshalable for Vec<u8> {
    open spec fn view_equal(&self, other: &Self) -> bool {
        self@ === other@
    }

    open spec fn is_marshalable(&self) -> bool {
        self@.len() <= usize::MAX && (self@.len() as usize).ghost_serialize().len()
            + self@.len() as int <= usize::MAX
    }

    open spec fn ghost_serialize(&self) -> Seq<u8> {
        (self@.len() as usize).ghost_serialize() + self@
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

    open spec fn ghost_serialize(&self) -> Seq<u8> {
        match self {
            None => seq![0],
            Some(x) => seq![1] + x.ghost_serialize(),
        }
    }
}

impl<T: Marshalable> Marshalable for Vec<T> {
    open spec fn view_equal(&self, other: &Self) -> bool {
        let s = self@;
        let o = other@;
        s.len() == o.len() && (forall|i: int|
            0 <= i < s.len() ==> #[trigger] s[i].view_equal(&o[i]))
    }

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
}

macro_rules!
    derive_marshalable_for_struct { { $(#[$attr : meta])* $pub : vis struct $newstruct :
    ident $(< $($poly : ident : Marshalable),+ $(,)? >)? { $($fieldvis : vis $field :
    ident : $fieldty : ty),+ $(,)? } } => { ::builtin_macros::verus! { impl $(< $($poly :
    Marshalable),* >)? Marshalable for $newstruct $(< $($poly),* >)? { open spec fn
    view_equal(& self, other : & Self) -> bool { $(&&& self.$field .view_equal(& other
    .$field))* } open spec fn is_marshalable(& self) -> bool { $(&&& self.$field
    .is_marshalable())* &&& 0 $(+ self.$field .ghost_serialize().len())* <= usize::MAX }
    open spec fn ghost_serialize(& self) -> Seq < u8 > { Seq::empty() $(+ self.$field
    .ghost_serialize())* } #[verifier::external_body] proof fn
    lemma_same_views_serialize_the_same(self : & Self, other : & Self) { unimplemented!()
    } } } } }

macro_rules! derive_marshalable_for_enum { { $(#[$attr : meta])* $pub : vis
    enum $newenum : ident $(< $($poly : ident : Marshalable),+ $(,)? >)? { $(#[tag = $tag
    : literal] $variant : ident $({ $(#[o =$memother : ident] $member : ident : $memberty
    : ty),* $(,)? })?),+ $(,)? } $([rlimit attr = $rlimitattr : meta])? } => {
    ::builtin_macros::verus! { impl $(< $($poly : Marshalable),+ >)? Marshalable for
    $newenum $(< $($poly),+ >)? { open spec fn view_equal(& self, other : & Self) -> bool
    { &&& match (self, other) { $(($newenum ::$variant $({ $($member),* })?, $newenum
    ::$variant $({ $($member : $memother),* })?) => { $($(&&& $member
    .view_equal($memother))*)? &&& true }),+ _ => false, } } open spec fn
    is_marshalable(& self) -> bool { &&& match self { $($newenum ::$variant $({
    $($member),* })? => { $($(&&& $member .is_marshalable())*)? &&& 1 $($(+ $member
    .ghost_serialize().len())*)? <= usize::MAX }),+ } } open spec fn ghost_serialize(&
    self) -> Seq < u8 > { match self { $($newenum ::$variant $({ $($member),* })? => {
    seq![$tag] $($(+ $member .ghost_serialize())*)? }),* } } #[verifier::external_body]
    proof fn lemma_same_views_serialize_the_same(self : & Self, other : & Self) {
    unimplemented!() } } } } }

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
    $marshalable { $forward } } impl Marshalable for $type { open spec fn view_equal(&
    self, other : & Self) -> bool { self
    .forward_bijection_for_view_equality_do_not_use_for_anything_else().view_equal(&
    other.forward_bijection_for_view_equality_do_not_use_for_anything_else()) } open spec
    fn is_marshalable($self : & Self) -> bool { $forward .is_marshalable() } open spec fn
    ghost_serialize($self : & Self) -> Seq < u8 > { $forward .ghost_serialize() }
    #[verifier::external_body] proof fn lemma_same_views_serialize_the_same(self : &
    Self, other : & Self) { unimplemented!() } } } } }

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

    #[verifier::external_body]
    pub fn static_params() -> (out: Parameters)
        ensures
            out@ == AbstractParameters::static_params(),
    {
        unimplemented!()
    }
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
    #[verifier::external_body]
    pub fn new() -> (e: CAckState)
        ensures
            e.num_packets_acked == 0,
            e.un_acked.len() == 0,
            e@ =~= AckState::new(),
    {
        unimplemented!()
    }

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

    #[verifier::external_body]
    pub fn get(&self, src: &EndPoint) -> (value: Option<&CAckState>)
        ensures
            value == match HashMap::get_spec(self.epmap@, src@) {
                Some(v) => Some(&v),
                None => None,
            },
            value is Some ==> self@.contains_key(src@),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub fn cack_state_swap(&mut self, src: &EndPoint, ack_state: &mut CAckState, default: CAckState)
        requires
            old(self).valid(),
            src.abstractable(),
        ensures
            HashMap::swap_spec(
                old(self).epmap@,
                self.epmap@,
                src@,
                *old(ack_state),
                *ack_state,
                default,
            ),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub fn put(&mut self, src: &EndPoint, value: CAckState)
        ensures
            HashMap::put_spec(old(self).epmap@, self.epmap@, src@, value),
    {
        unimplemented!()
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

    pub open spec fn put_spec(
        old_map_v: Map<AbstractEndPoint, V>,
        new_map_v: Map<AbstractEndPoint, V>,
        key: AbstractEndPoint,
        value: V,
    ) -> bool {
        new_map_v == old_map_v.insert(key, value)
    }

    pub open spec fn swap_spec(
        old_map_v: Map<AbstractEndPoint, V>,
        new_map_v: Map<AbstractEndPoint, V>,
        key: AbstractEndPoint,
        input_value: V,
        output_value: V,
        default_value: V,
    ) -> bool {
        &&& match Self::get_spec(old_map_v, key) {
            Some(v) => output_value == v,
            None => output_value == default_value,
        }
        &&& Self::put_spec(old_map_v, new_map_v, key, input_value)
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

#[verifier::ext_equal]
pub struct AckState<MT> {
    pub num_packets_acked: nat,
    pub un_acked: AckList<MT>,
}

impl AckState<Message> {
    pub open spec fn new() -> Self {
        AckState { num_packets_acked: 0, un_acked: seq![] }
    }
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
}

pub enum SingleMessage<MT> {
    Message { seqno: nat, dst: AbstractEndPoint, m: MT },
    Ack { ack_seqno: nat },
    InvalidMessage {  },
}

impl Ordering {
    pub open spec fn lt(self) -> bool {
        matches!(self, Ordering::Less)
    }
}

#[verifier::opaque]
pub open spec fn ckeyhashmap_max_serialized_size() -> usize {
    0x100000
}

impl Marshalable for CKeyHashMap {
    open spec fn view_equal(&self, other: &Self) -> bool {
        self@ === other@
    }

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

pub open spec(checked) fn valid_optional_value(ov: Option<AbstractValue>) -> bool {
    match ov {
        None => true,
        Some(value) => valid_value(value),
    }
}

pub trait VerusClone {

}

impl VerusClone for SHTKey {

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
    pub fn send_single_cmessage(&mut self, m: &CMessage, dst: &EndPoint) -> (sm: Option<
        CSingleMessage,
    >)
        requires
            old(self).valid(),
            old(self).abstractable(),
            m.abstractable(),
            m.message_marshallable(),
            m.is_marshalable(),
            dst@.valid_physical_address(),
        ensures
            self.valid(),
            match sm {
                Some(sm) => {
                    &&& sm.abstractable()
                    &&& sm is Message
                    &&& sm.arrow_Message_dst()@ == dst@
                    &&& SingleDelivery::send_single_message(
                        old(self)@,
                        self@,
                        m@,
                        dst@,
                        Some(sm@),
                        AbstractParameters::static_params(),
                    )
                    &&& sm.is_marshalable()
                },
                None => SingleDelivery::send_single_message(
                    old(self)@,
                    self@,
                    m@,
                    dst@,
                    None,
                    AbstractParameters::static_params(),
                ),
            },
    {
        let (num_packets_acked, un_acked_len) = match self.send_state.get(dst) {
            Some(ref cack_state) => {
                (cack_state.num_packets_acked, cack_state.un_acked.len() as u64)
            },
            None => { (0, 0) },
        };
        if Parameters::static_params().max_seqno - num_packets_acked == un_acked_len {
            return None;
        }
        let new_seqno = num_packets_acked + un_acked_len + 1;
        let sm_new = CSingleMessage::Message {
            seqno: new_seqno,
            dst: dst.clone_up_to_view(),
            m: m.clone_up_to_view(),
        };
        let mut local_state = CAckState::new();
        let default = CAckState::new();
        self.send_state.cack_state_swap(&dst, &mut local_state, default);
        local_state.un_acked.push(sm_new.clone_up_to_view());
        self.send_state.put(&dst, local_state);
        let ret = Some(sm_new);
        ret
    }
}

} // verus!
