extern crate verus_builtin_macros as builtin_macros;
use vstd::prelude::*;
use std::collections;
use std::time::SystemTime;
use vstd::bytes::*;
use vstd::map::*;

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
        CMessage::SetRequest { k, v } => Message::SetRequest { key: k, value: optional_value_view(v) },
        CMessage::Reply { k, v } => Message::Reply { key: k, value: optional_value_view(v) },
        CMessage::Redirect { k, id } => Message::Redirect { key: k, id: id@ },
        CMessage::Shard { kr, recipient } => Message::Shard { range: kr, recipient: recipient@ },
        CMessage::Delegate { range, h } => Message::Delegate { range: range, h: h@ },
    }
  }

}


pub open spec fn abstractify_cmessage_seq(messages: Seq<CSingleMessage>) -> Seq<SingleMessage<Message>> {
  messages.map_values(|msg: CSingleMessage| msg@)
}

impl CSingleMessage {

  pub open spec fn abstractable(self) -> bool {
    match self {
        CSingleMessage::Message { seqno: _, dst, m } => dst@.abstractable() && m.abstractable(),
        CSingleMessage::Ack { ack_seqno: _ } => true,
        CSingleMessage::InvalidMessage {} => true,
    }
  }

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


// File: marshal_v.rs
pub trait Marshalable : Sized {

  spec fn is_marshalable(&self) -> bool;

	#[verifier::external_body]
  spec fn ghost_serialize(&self) -> Seq<u8>
    recommends self.is_marshalable()
  {unimplemented!()}

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

impl<K: KeyTrait + VerusClone> DelegationMap<K> {

	#[verifier::external_body]
    pub closed spec fn view(self) -> Map<K,AbstractEndPoint> {
		unimplemented!()
	}


	#[verifier::external_body]
    pub closed spec fn valid(self) -> bool {
		unimplemented!()
	}


	#[verifier::external_body]
    pub fn new(k_zero: K, id_zero: ID) -> (s: Self)
        requires
            k_zero == K::zero_spec(),
            id_zero@.valid_physical_address(),
        ensures
            s.valid(),
            s@ == Map::total(|k: K| id_zero@),
	{
		unimplemented!()
	}

}


// File: host_impl_v.rs
pub struct Constants {
    pub root_identity: EndPoint,
    pub host_ids: Vec<EndPoint>,
    pub params: Parameters,
    pub me: EndPoint,
}

impl Constants {

    pub open spec fn view(self) -> AbstractConstants {
        AbstractConstants{
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
        AbstractParameters{
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

impl HostState {

    pub closed spec fn view(self) -> AbstractHostState
    {
        AbstractHostState{
            constants: self.constants@,
            delegation_map: AbstractDelegationMap(self.delegation_map@),
            h: self.h@,
            sd: self.sd@,
            received_packet: match self.received_packet {
                None => None,
                Some(cpacket) => Some(cpacket@),
                // TODO(tej): add map to Verus Option
                // received_packet.map(|cpacket| cpacket@),
            },
            num_delegations: self.num_delegations as int,
            received_requests: self.received_requests@,
        }
    }

    pub closed spec fn abstractable(&self) -> bool
    {
        self.constants.abstractable()
    }

    pub closed spec fn valid(&self) -> bool
    {
        &&& self.abstractable()
        &&& self.delegation_map.valid()
        // TODO why no valid_key?
        &&& (forall |k| self.h@.dom().contains(k) ==> #[trigger] valid_value(self.h@[k]))
        &&& self.sd.valid()
        &&& match &self.received_packet {
              Some(v) => v.abstractable() && v.msg is Message && v.dst@ == self.constants.me@,
              None => true,
          }
        &&& self.constants.valid()
        &&& self.num_delegations < self.constants.params.max_delegations
        // TODO why no delegation_map.lows
    }

    pub closed spec fn invariants(&self, netc_end_point: &AbstractEndPoint) -> bool
    {
        &&& self.next_action_index <3
        &&& self.delegation_map.valid()
        &&& self@.constants.me == netc_end_point
        &&& self.valid()
        &&& self@.constants.me.abstractable()
        &&& self.num_delegations < self.constants.params.max_delegations    // why did we move this here?
        &&& self.constants.params@ == AbstractParameters::static_params()
        &&& self.resend_count < 100000000
    }

	#[verifier::external_body]
    fn parse_command_line_configuration(args: &Args, me: EndPoint) -> (rc: Option<Constants>)
    ensures ({
        let abstract_end_points = parse_args(abstractify_args(*args));
        match rc {
            None => {
                ||| abstract_end_points.is_None()
                ||| abstract_end_points.unwrap().len()==0
                ||| !seq_is_unique(abstract_end_points.unwrap())
            },
            Some(c) => {
                &&& abstract_end_points.is_some()
                &&& abstract_end_points.unwrap().len() > 0
                &&& seq_is_unique(abstract_end_points.unwrap())
                &&& c@ == AbstractConstants{
                    root_identity: abstract_end_points.unwrap()[0],
                    host_ids: abstract_end_points.unwrap(),
                    params: AbstractParameters::static_params(),
                    me: me@ }
            }
        }
    })
	{
		unimplemented!()
	}

    pub fn real_init_impl(netc: &NetClient, args: &Args) -> (rc: Option<Self>)
    requires
        netc.valid(),
    ensures
        Self::init_ensures(netc, *args, rc),
    {
        let me = netc.get_my_end_point();
        let constants = /*Self -- Verus unimpl*/ HostState::parse_command_line_configuration(args, me);
        if matches!(constants, None) { return None; }
        let constants = constants.unwrap();
        let spare_root = constants.root_identity.clone_up_to_view();
        let zero_key = SHTKey::zero(); //SHTKey{ukey: 0};   // for some reason we can't make this call inside the ::new method below
        assert(SHTKey::zero_spec() == zero_key);
        let host_state = HostState{
            next_action_index: 0,
            resend_count: 0,
            constants: constants,
            delegation_map: DelegationMap::new(/*SHTKey::zero()*/ zero_key, spare_root),
            h: CKeyHashMap::new(),
            sd: CSingleDelivery::empty(),
            received_packet: None,
            num_delegations: 1,
            received_requests: Ghost(Seq::<AppRequest>::empty()),
        };
        let rc = Some(host_state);
        assert(netc.ok());
        assert(host_state.invariants(&netc.my_end_point())); // would pass some initial env state?
        assert(host_state@.delegation_map == AbstractDelegationMap::init(constants.root_identity@)) by {
            reveal(HostState::view);
            assert_maps_equal!(host_state.delegation_map@, AbstractDelegationMap::init(constants.root_identity@)@);
            assert(host_state.delegation_map@ == AbstractDelegationMap::init(constants.root_identity@)@);
        }
        assert(init(host_state@, netc.my_end_point(), abstractify_args(*args)));
        rc
    }

}


// File: single_delivery_state_v.rs
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

    pub open spec fn abstractable(&self) -> bool {
        forall |i: int| 0 <= i < self.un_acked.len() ==> #[trigger] self.un_acked[i].abstractable()
    }

    pub open spec fn no_acks_in_unacked(list: Seq<CSingleMessage>) -> bool {
        forall |i: int| 0 <= i < list.len() ==> #[trigger] list[i] is Message
    }

    pub open spec fn un_acked_list_sequential(list: Seq<CSingleMessage>) -> bool
        recommends Self::no_acks_in_unacked(list)
    {
        forall |i: int, j: int| #![auto] 0 <= i && j == i + 1 && j < list.len() ==>
            list[i].arrow_Message_seqno() as int + 1 == list[j].arrow_Message_seqno() as int
    }

    pub open spec fn un_acked_valid(msg: &CSingleMessage) -> bool {
        &&& msg is Message
        &&& msg.abstractable()
        &&& msg.is_marshalable()
    }

    pub open spec fn un_acked_list_valid(list: Seq<CSingleMessage>) -> bool {
        &&& forall |i:int| 0 <= i < list.len() ==> #[trigger] Self::un_acked_valid(&list[i])
        &&& Self::un_acked_list_sequential(list)
    }

    pub open spec fn un_acked_list_valid_for_dst(list: Seq<CSingleMessage>, dst: AbstractEndPoint) -> bool {
        &&& Self::un_acked_list_valid(list)
        &&& forall |i:int| 0 <= i < list.len() ==> (#[trigger] list[i].arrow_Message_dst())@ == dst
    }

    pub open spec fn valid_list(msgs: Seq<CSingleMessage>, num_packets_acked: int, dst: AbstractEndPoint) -> bool {
        &&& Self::un_acked_list_valid_for_dst(msgs, dst)
        &&& num_packets_acked as int + msgs.len() as int <= AbstractParameters::static_params().max_seqno
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
        forall |k: AbstractEndPoint| #[trigger] self@.contains_key(k) ==> k.valid_physical_address()
    }

    pub open spec fn view(&self) -> TombstoneTable {
        self.epmap@.map_values(|v: u64| v as nat)
    }

}


pub struct CSendState {
    pub epmap: HashMap<CAckState>
}

impl CSendState {

    pub open spec fn abstractable(&self) -> bool {
        forall |ep: EndPoint| #[trigger] self@.contains_key(ep@) ==> ep.abstractable() && self.epmap[&ep].abstractable()
        // NB ignoring the "ReverseKey" stuff from GenericRefinement.MapIsAbstractable
    }

    pub open spec fn valid(&self) -> bool {
        &&& self.abstractable()
        &&& forall |ep: AbstractEndPoint| #[trigger] self@.contains_key(ep) ==> self.epmap@[ep].valid(ep)
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

	#[verifier::external_body]
    pub fn empty() -> (out:Self)
    ensures out@ == SingleDelivery::<Message>::init()
	{
		unimplemented!()
	}

    pub open spec fn abstractable(&self) -> bool {
        &&& self.receive_state.abstractable()
        &&& self.send_state.abstractable()
    }

    pub open spec fn view(self) -> SingleDelivery<Message> {
        SingleDelivery {
            receive_state: self.receive_state@,
            send_state: self.send_state@,
        }
    }

    pub open spec fn valid(&self) -> bool {
        &&& self.abstractable()
        &&& self.send_state.valid()
    }

}


// File: abstract_end_point_t.rs
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


// File: abstract_parameters_t.rs
pub struct AbstractParameters {
    pub max_seqno: nat,
    pub max_delegations: nat,
}

impl AbstractParameters {

    pub open spec fn static_params() -> AbstractParameters
    {
        AbstractParameters {
            max_seqno: 0xffff_ffff_ffff_ffff as nat,
            max_delegations: 0x7FFF_FFFF_FFFF_FFFF as nat,
        }
    }

}


// File: abstract_service_t.rs
pub enum AppRequest {
    AppGetRequest{seqno:nat, key:AbstractKey},
    AppSetRequest{seqno:nat, key:AbstractKey, ov:Option<AbstractValue>},
}


// File: delegation_map_t.rs
#[verifier::ext_equal]  // effing INSAASAAAAANNE
pub struct AbstractDelegationMap(pub Map<AbstractKey, AbstractEndPoint>);

impl AbstractDelegationMap {

    pub open spec fn init(root_identity: AbstractEndPoint) -> Self
    {
        AbstractDelegationMap(Map::total(|k: AbstractKey| root_identity))
    }

    #[verifier(inline)]
    pub open spec fn view(self) -> Map<AbstractKey, AbstractEndPoint> {
        self.0
    }

}


// File: endpoint_hashmap_t.rs
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


// File: hashmap_t.rs
#[verifier(external_body)]
pub struct CKeyHashMap {
  m: collections::HashMap<CKey, Vec<u8>>,
}

impl CKeyHashMap {

    pub uninterp spec fn view(self) -> Map<AbstractKey, Seq<u8>>;

	#[verifier::external_body]
    #[verifier(external_body)]
    pub fn new() -> (out: CKeyHashMap)
        ensures out@ == Map::<AbstractKey, Seq<u8>>::empty()
	{
		unimplemented!()
	}

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


// File: host_protocol_t.rs
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
    pub num_delegations: int,   // TODO nat?
    pub received_requests: Seq<AppRequest>,
    // We decided to elide resendCount and nextActionIndex from this translated spec
    // because they're only relevant to liveness.
}

pub open spec fn parse_arg_as_end_point(arg: AbstractArg) -> AbstractEndPoint
{
    AbstractEndPoint{id: arg}
}

pub open spec fn unchecked_parse_args(args: AbstractArgs) -> Seq<AbstractEndPoint>
{
    args.map(|idx, arg: AbstractArg| parse_arg_as_end_point(arg))
}

pub open spec(checked) fn parse_args(args: AbstractArgs) -> Option<Seq<AbstractEndPoint>>
{
    let end_points = unchecked_parse_args(args);
    if forall |i| #![auto] 0 <= i < end_points.len() ==> end_points[i].valid_physical_address() {
        Some(end_points)
    } else {
        None
    }
}

pub open spec(checked) fn init(pre: AbstractHostState, id: AbstractEndPoint, args: AbstractArgs) -> bool {
    let end_points = parse_args(args);
    if end_points is None || end_points.unwrap().len()==0 {
        false
    } else {
        let root_identity = end_points.unwrap()[0];
        let params = AbstractParameters::static_params();
        pre == AbstractHostState{
            constants: AbstractConstants{root_identity, host_ids: end_points.unwrap(), params, me: id },
            delegation_map: AbstractDelegationMap::init(root_identity),
            h: Map::empty(),
            sd: SingleDelivery::init(),
            received_packet: None,
            num_delegations: 1,   // TODO nat?
            received_requests: seq![],
        }
    }
}


// File: io_t.rs
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


pub open spec fn abstractify_end_points(end_points: Vec<EndPoint>) -> Seq<AbstractEndPoint>
{
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
    pub closed spec fn state(&self) -> State
	{
		unimplemented!()
	}

    pub open spec fn ok(&self) -> bool
    {
        !(self.state() is Error)
    }

    pub open spec fn valid(&self) -> bool
    {
        &&& self.ok()
        &&& self.my_end_point().abstractable()
    }

	#[verifier::external_body]
    pub closed spec fn my_end_point(&self) -> AbstractEndPoint
	{
		unimplemented!()
	}

	#[verifier::external_body]
    pub fn get_my_end_point(&self) -> (ep: EndPoint)
        ensures
            ep@ == self.my_end_point()
	{
		unimplemented!()
	}

}


// File: keys_t.rs
pub trait KeyTrait : Sized {

    spec fn zero_spec() -> Self where Self: std::marker::Sized;

	#[verifier::external_body]
    fn zero() -> (z: Self)
        ensures z == Self::zero_spec()
        {
            unimplemented!()
        }
}


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

impl KeyTrait for SHTKey {

	#[verifier::external_body]
    fn zero() -> (z: Self)
	{
		unimplemented!()
	}

    open spec fn zero_spec() -> Self
    {
        SHTKey{ukey: 0}
    }

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


// File: single_delivery_t.rs
#[verifier::ext_equal]
pub struct AckState<MT> {
    pub num_packets_acked: nat,
    pub un_acked: AckList<MT>,
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


// File: seq_is_unique_v.rs
	#[verifier::opaque]
    pub open spec fn seq_is_unique<T>(s: Seq<T>) -> bool
    {
        forall |i: int, j: int| #![trigger s[i], s[j]] 0 <= i && i < s.len() && 0 <= j && j < s.len() && s[i] == s[j] ==> i == j
    }


// File: app_interface_t.rs
pub open spec fn max_val_len() -> int { 1024 }

pub open spec fn valid_value(value: AbstractValue) -> bool { value.len() < max_val_len() }


// File: args_t.rs
pub open spec fn abstractify_args(args: Args) -> AbstractArgs
{
    args@.map(|i, arg: Arg| arg@)
}


// File: host_impl_t.rs
impl HostState {

    pub open spec fn init_ensures(netc: &NetClient, args: Args, rc: Option<Self>) -> bool
    {
        match rc {
            None => true,
            Some(host_state) => {
                &&& netc.ok()   // port of env.ok.ok()
                &&& host_state.invariants(&netc.my_end_point())
                &&& init(host_state@, netc.my_end_point(), abstractify_args(args))
            }
        }
    }

}


pub trait VerusClone {}

impl VerusClone for SHTKey {}

///////

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

pub type LSHTPacket = LPacket<AbstractEndPoint, SingleMessage<Message>>;
pub type AckList<MT> = Seq<SingleMessage<MT>>;
pub type PMsg = SingleMessage<Message>;
pub type SendState<MT> = Map<AbstractEndPoint, AckState<MT>>;
pub type TombstoneTable = Map<AbstractEndPoint, nat>;

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

pub type NetEvent = LIoOp<AbstractEndPoint, Seq<u8>>;
pub type NetPacket = LPacket<AbstractEndPoint, Seq<u8>>;

pub type History = Seq<NetEvent>;

#[verifier(external_body)]
pub struct NetClientCPointers {
    get_time_func: extern "C" fn() -> u64,
    receive_func: extern "C" fn(i32, *mut bool, *mut bool, *mut *mut std::vec::Vec<u8>, *mut *mut std::vec::Vec<u8>),
    send_func: extern "C" fn(u64, *const u8, u64, *const u8) -> bool
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


}
