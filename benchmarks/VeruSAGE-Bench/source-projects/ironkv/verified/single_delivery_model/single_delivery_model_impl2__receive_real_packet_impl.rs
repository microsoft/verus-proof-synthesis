extern crate verus_builtin_macros as builtin_macros;
use vstd::map::*;
use vstd::prelude::*;
use std::collections;
use vstd::bytes::*;

fn main() {}

verus! {

pub open spec fn outbound_packet_is_valid(cpacket: &CPacket) -> bool
{
    &&& cpacket.abstractable()  // CPacketIsAbstractable
    &&& cpacket.msg.is_marshalable()   // CSingleMessageMarshallable
    &&& !(cpacket.msg is InvalidMessage) // (out.msg.CSingleMessage? || out.msg.CAck?)
}


pub open spec fn valid_ack(ack: CPacket, original: CPacket) -> bool {
    &&& ack.abstractable()
    &&& outbound_packet_is_valid(&ack)  // how does this relate to abstractable?
    &&& ack.src@ == original.dst@
    &&& ack.dst@ == original.src@
}

pub type Hashtable = Map<AbstractKey, AbstractValue>;

    #[derive(Eq,PartialEq,Hash)]
pub struct SHTKey {
    pub // workaround
        ukey: u64,
}

impl SHTKey {}

pub type AbstractKey = SHTKey;
pub type AbstractValue = Seq<u8>;
pub type CKey = SHTKey;

#[verifier(external_body)]
pub struct CKeyHashMap {
  m: collections::HashMap<CKey, Vec<u8>>,
}

impl CKeyHashMap{
    pub uninterp spec fn view(self) -> Map<AbstractKey, Seq<u8>>;

    #[verifier::external_body]
    #[verifier(when_used_as_spec(spec_to_vec))]
    pub fn to_vec(&self) -> (res: Vec<CKeyKV>)
      ensures res == self.spec_to_vec()
    {
        unimplemented!()
    }

    pub uninterp spec fn spec_to_vec(&self) -> Vec<CKeyKV>;
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

pub open spec fn abstractify_cmessage_seq(messages: Seq<CSingleMessage>) -> Seq<SingleMessage<Message>> {
  messages.map_values(|msg: CSingleMessage| msg@)

}
pub struct KeyRange<K: KeyTrait + VerusClone>{
    pub lo: KeyIterator<K>,
    pub hi: KeyIterator<K>,
}

pub struct KeyIterator<K: KeyTrait + VerusClone>{
    // None means we hit the end
    pub k: Option<K>,
}

impl<K: VerusClone + KeyTrait> VerusClone for KeyIterator<K> {}

pub trait KeyTrait : Sized {}
pub trait VerusClone : Sized {}


impl<K: VerusClone + KeyTrait> VerusClone for KeyRange<K> {}

impl KeyTrait for SHTKey { }
impl VerusClone for SHTKey {}

// #[derive(Copy, Clone)]
#[derive(PartialEq, Eq, Hash)]
pub struct EndPoint {
    pub id: Vec<u8>,
}

impl EndPoint {
    #[verifier::external_body]
    pub fn clone_up_to_view(&self) -> (res: EndPoint)
        ensures res@ == self@
    {
        unimplemented!()
    }

    pub open spec fn view(self) -> AbstractEndPoint {
        AbstractEndPoint{id: self.id@}
    }

        #[verifier(inline)]
    pub open spec fn abstractable(self) -> bool {
        self@.valid_physical_address()
    }

}

pub struct AbstractEndPoint {
    pub id: Seq<u8>,
}

impl AbstractEndPoint{

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

impl<V> HashMap<V>
{
    pub uninterp spec fn view(self) -> Map<AbstractEndPoint, V>;

        #[verifier::external_body]
    pub fn insert(&mut self, key: &EndPoint, value: V)
      ensures self@ == old(self)@.insert(key@, value)
        {
                unimplemented!()
        }

    #[verifier(external_body)]
    pub fn new() -> (out: Self)
        ensures out@ == Map::<AbstractEndPoint, V>::empty()
    {
      HashMap { m: collections::HashMap::new() }
    }

    pub open spec fn spec_index(self, key: &EndPoint) -> V
    recommends
        self@.contains_key(key@),
    {
        self@[key@]
    }
}

pub type TombstoneTable = Map<AbstractEndPoint, nat>;

pub type AckList<MT> = Seq<SingleMessage<MT>>;

pub struct AckState<MT> {
    pub num_packets_acked: nat,
    pub un_acked: AckList<MT>,
}

impl AckState<Message> {
    //pub spec fn abstractable
    pub open spec fn new() -> Self {
        AckState{ num_packets_acked: 0, un_acked: seq![] }
    }
}

/// translates `AckState<MT = CMessage>` (that is, we specialize the message type)
#[verifier::ext_equal]  // effing INSAASAAAAANNE
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

    /// Translates CAckStateIsValid
    pub open spec fn valid(&self, dst: AbstractEndPoint) -> bool {
        &&& self.abstractable()
        &&& Self::valid_list(self.un_acked@, self.num_packets_acked as int, dst)
    }
    pub open spec fn abstractable(&self) -> bool {
        forall |i: int| 0 <= i < self.un_acked.len() ==> #[trigger] self.un_acked[i].abstractable()
    }

    pub open spec fn valid_list(msgs: Seq<CSingleMessage>, num_packets_acked: int, dst: AbstractEndPoint) -> bool {
        &&& Self::un_acked_list_valid_for_dst(msgs, dst)
        &&& num_packets_acked as int + msgs.len() as int <= AbstractParameters::static_params().max_seqno
        &&& (msgs.len() > 0 ==> msgs[0].arrow_Message_seqno() == num_packets_acked + 1)
    }

    pub open spec fn un_acked_list_valid_for_dst(list: Seq<CSingleMessage>, dst: AbstractEndPoint) -> bool {
        &&& Self::un_acked_list_valid(list)
        &&& forall |i:int| 0 <= i < list.len() ==> (#[trigger] list[i].arrow_Message_dst())@ == dst
    }

    pub open spec fn un_acked_list_valid(list: Seq<CSingleMessage>) -> bool {
        &&& forall |i:int| 0 <= i < list.len() ==> #[trigger] Self::un_acked_valid(&list[i])
        &&& Self::un_acked_list_sequential(list)
    }

    pub open spec fn un_acked_list_sequential(list: Seq<CSingleMessage>) -> bool
        recommends Self::no_acks_in_unacked(list)
    {
        forall |i: int, j: int| #![auto] 0 <= i && j == i + 1 && j < list.len() ==>
            list[i].arrow_Message_seqno() as int + 1 == list[j].arrow_Message_seqno() as int
    }

    pub open spec fn no_acks_in_unacked(list: Seq<CSingleMessage>) -> bool {
        forall |i: int| 0 <= i < list.len() ==> #[trigger] list[i] is Message
    }

    pub open spec fn un_acked_valid(msg: &CSingleMessage) -> bool {
        &&& msg is Message
        &&& msg.abstractable()
        &&& msg.is_marshalable()
    }



}

pub open spec fn tombstone_table_lookup(src: AbstractEndPoint, t: TombstoneTable) -> nat
{
    if t.dom().contains(src) { t[src] } else { 0 }
}


pub struct CTombstoneTable {
    pub epmap: HashMap<u64>,
}

impl CTombstoneTable {
    pub open spec fn abstractable(&self) -> bool {
        forall |k: AbstractEndPoint| #[trigger] self@.contains_key(k) ==> k.valid_physical_address()
    }


    /// Since I'm a map, I already have a simple view(), hence the special name.
    pub open spec fn view(&self) -> TombstoneTable {
        self.epmap@.map_values(|v: u64| v as nat)
    }

    #[verifier::external_body]
    pub fn lookup(&self, src: &EndPoint) -> (last_seqno: u64)
    ensures
        last_seqno as int == tombstone_table_lookup(src@, self@),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub fn insert(&mut self, src: &EndPoint, last_seqno: u64)
    requires
        old(self).abstractable(),
        src@.valid_physical_address(),
    ensures
        self@ =~= old(self)@.insert(src@, last_seqno as nat),
        self.abstractable(),
    {
        unimplemented!()
    }

}

#[allow(inconsistent_fields)]
pub enum CMessage {
  GetRequest{ k: CKey},
  SetRequest{ k: CKey, v: Option::<Vec<u8>>},
  Reply{ k: CKey, v: Option::<Vec::<u8>> },
  Redirect{ k: CKey, id: EndPoint },
  Shard{ kr: KeyRange::<CKey>, recipient: EndPoint },
  Delegate{ range: KeyRange::<CKey>, h: CKeyHashMap},
}

impl CMessage{
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

    pub open spec fn abstractable(self) -> bool {
    match self {
        CMessage::Redirect { k, id } => id@.abstractable(),
        CMessage::Shard { kr, recipient } => recipient@.abstractable(),
        _ => true,
    }
  }
}

pub open spec fn optional_value_view(ov: Option::<Vec::<u8>>) -> Option::<Seq::<u8>>
{
    match ov {
        Some(v) => Some(v@),
        None => None,
    }
}

pub type PMsg = SingleMessage<Message>;

/// A Packet is an abstract version of a `CPacket`.
///
/// It's isomorphic to an `LSHTPacket = LPacket<AbstractEndPoint,
/// SingleMessage<Message>>`.
pub struct Packet {
    pub dst: AbstractEndPoint,
    pub src: AbstractEndPoint,
    pub msg: PMsg,
}

pub struct CPacket {
  pub dst: EndPoint,
  pub src: EndPoint,
  pub msg: CSingleMessage,
}

impl CPacket {
  pub open spec fn valid(self) -> bool {
    &&& self.msg.temp_valid()
  }

  // Translates Impl/SHT/PacketParsing.i.dfy :: AbstractifyCPacketToShtPacket
  pub open spec fn view(self) -> Packet {
    Packet { dst: self.dst@, src: self.src@, msg: self.msg@ }
  }

  pub open spec fn abstractable(self) -> bool {
    &&& self.dst.abstractable()
    &&& self.src.abstractable()
    &&& self.msg.abstractable()
  }
}


pub struct AbstractParameters {
    pub max_seqno: nat,
    pub max_delegations: nat,
}

impl AbstractParameters{
    pub open spec fn static_params() -> AbstractParameters
    {
        AbstractParameters {
            max_seqno: 0xffff_ffff_ffff_ffff as nat,
            max_delegations: 0x7FFF_FFFF_FFFF_FFFF as nat,
        }
    }
}

impl CSingleMessage{
  pub open spec fn view(self) -> SingleMessage<Message> {
    match self {
        CSingleMessage::Message { seqno, dst, m } => SingleMessage::Message { seqno: seqno as nat, dst: dst@, m: m@ },
        CSingleMessage::Ack { ack_seqno } => SingleMessage::Ack { ack_seqno: ack_seqno as nat },
        CSingleMessage::InvalidMessage { } => SingleMessage::InvalidMessage {  },
    }
  }

  pub open spec fn abstractable(self) -> bool {
    match self {
        CSingleMessage::Message { seqno: _, dst, m } => dst@.abstractable() && m.abstractable(),
        CSingleMessage::Ack { ack_seqno: _ } => true,
        CSingleMessage::InvalidMessage {} => true,
    }
  }

  pub open spec fn temp_valid(&self) -> bool {
    match self {
        CSingleMessage::Message { seqno, .. } => seqno < AbstractParameters::static_params().max_seqno,
        CSingleMessage::Ack { ack_seqno } => ack_seqno < AbstractParameters::static_params().max_seqno,
        CSingleMessage::InvalidMessage { } => false,
    }
  }

}

pub type SendState<MT> = Map<AbstractEndPoint, AckState<MT>>;

pub struct CSendState {
    pub epmap: HashMap<CAckState>
}

impl CSendState {
    /// CSendStateIsAbstractable
    pub open spec fn abstractable(&self) -> bool {
        forall |ep: EndPoint| #[trigger] self@.contains_key(ep@) ==> ep.abstractable() && self.epmap[&ep].abstractable()
        // NB ignoring the "ReverseKey" stuff from GenericRefinement.MapIsAbstractable
    }

    /// CSendStateIsValid
    pub open spec fn valid(&self) -> bool {
        &&& self.abstractable()
        &&& forall |ep: AbstractEndPoint| #[trigger] self@.contains_key(ep) ==> self.epmap@[ep].valid(ep)
    }


    pub open spec fn view(&self) -> SendState<Message> {
        self.epmap@.map_values(|v: CAckState| v@)
    }

}

#[verifier::ext_equal]
pub struct SingleDelivery<MT> {
    pub receive_state: TombstoneTable,
    pub send_state: SendState<MT>
}

impl<MT> SingleDelivery<MT> {
    pub open spec fn init() -> Self
    {
        SingleDelivery{ receive_state: Map::empty(), send_state: Map::empty() }
    }
    /// Protocol/SHT/SingleDelivery.i.dfy ReceiveRealPacket
    pub open spec(checked) fn receive_real_packet(self, post: Self, pkt: Packet) -> bool {
        if self.new_single_message(pkt) {
            let last_seqno = tombstone_table_lookup(pkt.src, self.receive_state);
            // Mark it received
            post == Self{ receive_state: self.receive_state.insert(pkt.src, (last_seqno + 1) as nat), ..self }
        } else {
            post == self
        }
    }


    /// Protocol/SHT/SingleDelivery.i.dfy NewSingleMessage
    pub open spec(checked) fn new_single_message(self, pkt: Packet) -> bool {
        let last_seqno = tombstone_table_lookup(pkt.src, self.receive_state);
        &&& pkt.msg is Message
        &&& pkt.msg.arrow_Message_seqno() == last_seqno + 1
    }

 
    pub open spec(checked) fn maybe_ack_packet(pre: Self, pkt: Packet, ack: Packet, acks:Set<Packet>) -> bool {
        if pre.should_ack_single_message(pkt) {
            pre.send_ack(pkt, ack, acks)
        } else {
            acks.is_empty()
        }
    }

    pub open spec(checked) fn should_ack_single_message(self, pkt: Packet) -> bool
    {
        &&& pkt.msg is Message  // Don't want to ack acks
        &&& {
            let last_seqno = tombstone_table_lookup(pkt.src, self.receive_state);
            pkt.msg.arrow_Message_seqno() <= last_seqno
            }
    }

    /// Protocol/SHT/SingleDelivery.i.dfy SendAck
    pub open spec(checked) fn send_ack(self, pkt: Packet, ack: Packet, acks:Set<Packet>) -> bool
    recommends
        self.should_ack_single_message(pkt),
    {
        &&& ack.msg is Ack
        &&& ack.msg.arrow_Ack_ack_seqno() == pkt.msg.arrow_Message_seqno()
        &&& ack.src == pkt.dst
        &&& ack.dst == pkt.src
        &&& acks == set![ ack ]
    }


}

impl SingleDelivery<Message> {
    pub open spec(checked) fn un_acked_messages_for_dest_up_to(self, src: AbstractEndPoint, dst: AbstractEndPoint, count: nat) -> Set<Packet>
    recommends
        self.send_state.contains_key(dst),
        count <= self.send_state[dst].un_acked.len()
    {
        Set::new(|p: Packet| {
                &&& p.src == src
                &&& exists |i: int| {
                    &&& 0 <= i < count
                    &&& self.send_state[dst].un_acked[i] is Message
                    &&& p.msg == self.send_state[dst].un_acked[i]
                    &&& p.dst == p.msg.arrow_Message_dst()
                }
        })
    }
}


/// Translates CSingleDeliveryAcct
pub struct CSingleDelivery {
    pub receive_state: CTombstoneTable,
    pub send_state: CSendState,
}


impl CSingleDelivery {

    /// Translates AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct
    pub open spec fn view(self) -> SingleDelivery<Message> {
        SingleDelivery {
            receive_state: self.receive_state@,
            send_state: self.send_state@,
        }
    }

    /// Translates CSingleDeliveryAccountIsValid
    pub open spec fn abstractable(&self) -> bool {
        &&& self.receive_state.abstractable()
        &&& self.send_state.abstractable()
    }


    pub open spec fn option_cpacket_to_set_packet(opt_pkt: Option<CPacket>) -> Set<Packet>
    {
        match opt_pkt {
            Some(pkt) => set!{pkt@},
            None => Set::<Packet>::empty(),
        }
    }

    /// Translates CSingleDeliveryAccountIsValid
    pub open spec fn valid(&self) -> bool {
        &&& self.abstractable()
            &&& self.send_state.valid()
    }



    pub fn receive_real_packet_impl(&mut self, pkt: &CPacket) -> (packet_is_fresh: bool)
    requires
        old(self).valid(),
        pkt.abstractable(),
        pkt.msg is Message,
    ensures
        self.valid(),
        SingleDelivery::receive_real_packet(old(self)@, self@, pkt@),
        packet_is_fresh == SingleDelivery::new_single_message(old(self)@, pkt@),
    {
        // We inlined NewSingleMessageImpl here.
        let last_seqno = self.receive_state.lookup(&pkt.src);
        match pkt.msg {
            CSingleMessage::Message{seqno: pkt_seqno, ..} => {
                let packet_is_fresh = pkt_seqno > 0 && pkt_seqno - 1 == last_seqno;
                if packet_is_fresh {
                    self.receive_state.insert(&pkt.src, last_seqno + 1);
                }
                packet_is_fresh 
            }
            _ => { assert(false); unreached() }
        }

    }
}

/*=====marshalable=================*/
pub trait Marshalable : Sized {
  spec fn view_equal(&self, other: &Self) -> bool;
  spec fn is_marshalable(&self) -> bool;
  spec fn ghost_serialize(&self) -> Seq<u8>
    recommends self.is_marshalable();
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
    self@.len() <= usize::MAX &&
    (self@.len() as usize).ghost_serialize().len() + self@.len() as int <= usize::MAX
  }

  open spec fn ghost_serialize(&self) -> Seq<u8> {
    (self@.len() as usize).ghost_serialize()
      + self@
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
}

// NOTE: This can be replaced with a `define_struct_and_derive_marshalable` invocation
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
      }
    }
  }
}

/// `derive_marshalable_for_enum` is a macro that implements [`Marshalable`] for a enum. You
/// probably want to use [`define_enum_and_derive_marshalable`] wherever possible instead, since it
/// prevents code duplication. However, if you are (for some reason) unable to define at the enum
/// definition site, then this macro lets you derive the macro by simply (textually) copy-pasting
/// the enum.
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
      }
    }
  }
}



/// `define_enum_and_derive_marshalable` is a macro that, well, defines an enum, and implements
/// [`Marshalable`] on it. This is intended to make it easier to produce serializers and
/// deserializers for arbitrary types (including polymorphic ones).
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
pub(crate) use define_enum_and_derive_marshalable;


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
            }
        }
    }
}

    /* $line_count$Proof$ */ marshalable_by_bijection! {
    /* $line_count$Proof$ */     [SHTKey] <-> [u64];
    /* $line_count$Proof$ */     forward(self) self.ukey;
    /* $line_count$Proof$ */     backward(x) SHTKey { ukey: x };
    /* $line_count$Proof$ */ }

    impl SHTKey {
        /// Document that view_equal is definitionally to ==, with no explicit proof required.
        pub proof fn view_equal_spec()
            ensures forall |x: &SHTKey, y: &SHTKey| #[trigger] x.view_equal(y) <==> x == y
        {
        }
    }

    /* $line_count$Proof$}$ */ marshalable_by_bijection! {
    /* $line_count$Proof$}$ */    [EndPoint] <-> [Vec::<u8>];
    /* $line_count$Proof$}$ */    forward(self) self.id;
    /* $line_count$Proof$}$ */    backward(x) EndPoint { id: x };
    /* $line_count$Proof$}$ */ }

    impl EndPoint {
        /// Document that view_equal is definitially x@ == y@, with no explicit proof required.
        pub proof fn view_equal_spec()
            ensures forall |x: &EndPoint, y: &EndPoint| #[trigger] x.view_equal(y) <==> x@ == y@
        {
        }
    }

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

    /* $line_count$Proof$ */ derive_marshalable_for_struct! {
    /* $line_count$Proof$ */     pub struct CKeyKV {
    /* $line_count$Proof$ */         pub k: CKey,
    /* $line_count$Proof$ */         pub v: Vec::<u8>,
    /* $line_count$Proof$ */     }
    /* $line_count$Proof$ */ }

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

/* $line_count$Proof$ */ define_enum_and_derive_marshalable! {
/* $line_count$Exec$ */ pub enum CSingleMessage {                                                                           /* $line_count$Exec$ */   #[tag = 0]
/* $line_count$Exec$ */   Message{ #[o=o0] seqno: u64, #[o=o1] dst: EndPoint, #[o=o2] m: CMessage },
/* $line_count$Exec$ */   #[tag = 1]
/* $line_count$Exec$ */   // I got everything up to and including `ack_seqno`
/* $line_count$Exec$ */   Ack{ #[o=o0] ack_seqno: u64},
/* $line_count$Exec$ */   #[tag = 2]
/* $line_count$Exec$ */   InvalidMessage,
/* $line_count$Exec$ */ }
/* $line_count$Proof$ */ [rlimit attr = verifier::rlimit(25)]
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
}




}
