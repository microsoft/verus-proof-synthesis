extern crate verus_builtin_macros as builtin_macros;
use vstd::prelude::*;
use vstd::bytes::*;
use vstd::set_lib::*;
use std::collections;

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

}


pub struct CPacket {
  pub dst: EndPoint,
  pub src: EndPoint,
  pub msg: CSingleMessage,
}


// File: marshal_v.rs
pub trait Marshalable : Sized {

  spec fn is_marshalable(&self) -> bool;

  spec fn ghost_serialize(&self) -> Seq<u8>;

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
    self@.len() <= usize::MAX &&
    (self@.len() as usize).ghost_serialize().len() + self@.len() as int <= usize::MAX
  }

  open spec fn ghost_serialize(&self) -> Seq<u8> {
    (self@.len() as usize).ghost_serialize()
      + self@
  }

}


impl<T: Marshalable> Marshalable for Option<T> {

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


impl<T: Marshalable> Marshalable for Vec<T> {

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


// File: delegation_map_v.rs
#[verifier::reject_recursive_types(K)]
pub struct DelegationMap<K: KeyTrait + VerusClone> {
    // Our efficient implementation based on ranges
    lows: StrictlyOrderedMap<K>,
    // Our spec version
    m: Ghost<Map<K, AbstractEndPoint>>,

}


// File: host_impl_v.rs
pub struct Constants {
    pub root_identity: EndPoint,
    pub host_ids: Vec<EndPoint>,
    pub params: Parameters,
    pub me: EndPoint,
}

pub struct Parameters {
    pub max_seqno: u64,
    pub max_delegations: u64,
}

pub open spec fn abstractify_raw_log_to_ios(rawlog: Seq<NetEvent>) -> Seq<LSHTIo>
{
  rawlog.map_values(|evt: NetEvent| abstractify_net_event_to_lsht_io(evt))
}

pub fn make_empty_event_results() -> (res: Ghost<EventResults>)
    ensures
        res@.recvs == Seq::<NetEvent>::empty(),
        res@.clocks == Seq::<NetEvent>::empty(),
        res@.sends == Seq::<NetEvent>::empty(),
        res@.ios == Seq::<NetEvent>::empty(),
        extract_packets_from_abstract_ios(abstractify_raw_log_to_ios(res@.ios)) == Set::<Packet>::empty(),
{
    let ghost res = EventResults {
        recvs: Seq::<NetEvent>::empty(),
        clocks: Seq::<NetEvent>::empty(),
        sends: Seq::<NetEvent>::empty(),
        ios: Seq::<NetEvent>::empty(),
    };
    proof {
        assert_sets_equal!(extract_packets_from_abstract_ios(abstractify_raw_log_to_ios(res.ios)),
                           Set::<Packet>::empty());
    };
    Ghost(res)
}

pub struct HostState {
    // Fields from Impl/LiveSHT/SchedulerImpl::SchedulerImpl
    next_action_index: u64,
    resend_count: u64,

    // Fields from Impl/SHT/HostState::HostState
    constants: Constants,
    delegation_map: DelegationMap<CKey>,
    h: CKeyHashMap,
    sd: CSingleDelivery,
    received_packet: Option<CPacket>,
    num_delegations: u64,
    received_requests: Ghost<Seq<AppRequest>>,
}


// File: single_delivery_state_v.rs
#[verifier::ext_equal]  // effing INSAASAAAAANNE
pub struct CAckState {
    pub num_packets_acked: u64,
    pub un_acked: Vec<CSingleMessage>,
}

pub struct CTombstoneTable {
    pub epmap: HashMap<u64>,
}

pub struct CSendState {
    pub epmap: HashMap<CAckState>
}

pub struct CSingleDelivery {
    pub receive_state: CTombstoneTable,
    pub send_state: CSendState,
}


// File: abstract_end_point_t.rs
pub struct AbstractEndPoint {
    pub id: Seq<u8>,
}


// File: abstract_service_t.rs
pub enum AppRequest {
    AppGetRequest{seqno:nat, key:AbstractKey},
    AppSetRequest{seqno:nat, key:AbstractKey, ov:Option<AbstractValue>},
}


// File: endpoint_hashmap_t.rs
#[verifier::accept_recursive_types(V)]
#[verifier(external_body)]
pub struct HashMap<V> {
  m: collections::HashMap<EndPoint, V>,
}


// File: environment_t.rs
pub struct LPacket<IdType, MessageType> {
    pub dst: IdType,
    pub src: IdType,
    pub msg: MessageType,
}

pub enum LIoOp<IdType, MessageType> {
    Send{s: LPacket<IdType, MessageType>},
    Receive{r: LPacket<IdType, MessageType>},
    TimeoutReceive{},
    ReadClock{t: int},
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
      ensures res == self.spec_to_vec()
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
    // ckeykvlt ensures that this forall does not create a trigger loop on
    // v@[i].k.ukey, v@[i+1].k.ukey, ...
    //
    // we weren't able to fix this by making the whole < the trigger
    forall |i: int, j: int| 0 <= i && i + 1 < v.len() && j == i+1 ==> #[trigger] ckeykvlt(v@[i], v@[j])
}


// File: host_impl_t.rs
pub struct EventResults {
    // What netc actually observed:
    pub recvs: Seq<NetEvent>,
    pub clocks: Seq<NetEvent>,
    pub sends: Seq<NetEvent>,

    /// What we were trying to make happen:
    /// ios may claim an event that doesn't appear in event_seq() if, say, the netc socket broke on
    /// send. We already received, so the only way we can refine is by claiming we finished the
    /// corresponding send (in ios). In this case, the postcondition of next_ensures gives
    /// us the out because !netc.ok allows ios!=event_seq().
    pub ios: Ios,
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


// File: network_t.rs
pub struct Packet {
    pub dst: AbstractEndPoint,
    pub src: AbstractEndPoint,
    pub msg: PMsg,
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


// File: net_sht_v.rs
pub open spec fn net_packet_is_abstractable(net: NetPacket) -> bool
{
    true
}

pub open spec fn net_event_is_abstractable(evt: NetEvent) -> bool
{
    match evt {
      LIoOp::<AbstractEndPoint, Seq<u8>>::Send{s} => net_packet_is_abstractable(s),
      LIoOp::<AbstractEndPoint, Seq<u8>>::Receive{r} => net_packet_is_abstractable(r),
      LIoOp::<AbstractEndPoint, Seq<u8>>::TimeoutReceive{} => true,
      LIoOp::<AbstractEndPoint, Seq<u8>>::ReadClock{t} => true,
    }
}

pub open spec fn sht_demarshal_data(data: Seq<u8>) -> CSingleMessage
    recommends exists |v: CSingleMessage| v.is_marshalable() && v.ghost_serialize() == data
{
    let v = choose |v: CSingleMessage| v.is_marshalable() && v.ghost_serialize() == data;
    v
}

pub open spec fn abstractify_net_packet_to_lsht_packet(net: NetPacket) -> LSHTPacket
    recommends net_packet_is_abstractable(net)
{
    LPacket {
        dst: net.dst,
        src: net.src,
        msg: (sht_demarshal_data(net.msg))@
    }
}

pub open spec fn abstractify_net_event_to_lsht_io(evt: NetEvent) -> LSHTIo
    recommends net_event_is_abstractable(evt)
{
    match evt {
        LIoOp::<AbstractEndPoint, Seq<u8>>::Send{s} =>
          LIoOp::<AbstractEndPoint, SingleMessage<Message>>::Send{ s: abstractify_net_packet_to_lsht_packet(s) },
        LIoOp::<AbstractEndPoint, Seq<u8>>::Receive{r} =>
          LIoOp::<AbstractEndPoint, SingleMessage<Message>>::Receive{ r: abstractify_net_packet_to_lsht_packet(r) },
        LIoOp::<AbstractEndPoint, Seq<u8>>::TimeoutReceive{} =>
          LIoOp::<AbstractEndPoint, SingleMessage<Message>>::TimeoutReceive{},
        LIoOp::<AbstractEndPoint, Seq<u8>>::ReadClock{t} =>
          LIoOp::<AbstractEndPoint, SingleMessage<Message>>::ReadClock{ t: t as int },
    }
}


// File: host_protocol_t.rs
pub open spec fn extract_sent_packets_from_ios(ios: Seq<LSHTIo>) -> Seq<LSHTPacket>
{
    ios.filter(|io: LSHTIo| io is Send).map_values(|io: LSHTIo| io.arrow_Send_s())
}

pub open spec fn extract_packet_from_lsht_packet(lp: LSHTPacket) -> Packet
{
    Packet { dst: lp.dst, src: lp.src, msg: lp.msg }
}

pub open spec fn extract_packets_from_lsht_packets(seq_packets: Seq<LSHTPacket>) -> Set<Packet>
{
  seq_packets.map_values(|lp: LSHTPacket| extract_packet_from_lsht_packet(lp)).to_set()
}

pub open spec fn extract_packets_from_abstract_ios(ios: AbstractIos) -> Set<Packet>
{
    extract_packets_from_lsht_packets(extract_sent_packets_from_ios(ios))
}


pub trait KeyTrait {}

pub trait VerusClone {}

impl VerusClone for SHTKey {}


impl KeyTrait for SHTKey {}

///////////////////////////
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

// Stores the entries from smallest to largest
struct StrictlyOrderedVec<K: KeyTrait> {
    v: Vec<K>,
}

pub type Arg = Vec<u8>;
pub type Args = Vec<Arg>;

pub type AbstractArg = Seq<u8>;
pub type AbstractArgs = Seq<AbstractArg>;

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

pub type AbstractIos = Seq<LSHTIo>;
pub type LSHTPacket = LPacket<AbstractEndPoint, SingleMessage<Message>>;
pub type LSHTIo = LIoOp<AbstractEndPoint, SingleMessage<Message>>;
pub type NetEvent = LIoOp<AbstractEndPoint, Seq<u8>>;
pub type NetPacket = LPacket<AbstractEndPoint, Seq<u8>>;
type Ios = Seq<NetEvent>;
pub type PMsg = SingleMessage<Message>;

//for marshal
    /* $line_count$Proof$}$ */ marshalable_by_bijection! {
    /* $line_count$Proof$}$ */    [EndPoint] <-> [Vec::<u8>];
    /* $line_count$Proof$}$ */    forward(self) self.id;
    /* $line_count$Proof$}$ */    backward(x) EndPoint { id: x };
    /* $line_count$Proof$}$ */ }


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

