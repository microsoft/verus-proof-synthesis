
extern crate verus_builtin_macros as builtin_macros;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::set_lib::*;
use vstd::bytes::*;
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

  pub open spec fn message_marshallable(&self) -> bool
  {
      match self {
          CMessage::GetRequest{ k } => valid_key(*k),
          CMessage::SetRequest{ k , v } => valid_key(*k) && valid_optional_value(optional_value_view(*v)),
          CMessage::Reply{ k, v } => valid_key(*k) && valid_optional_value(optional_value_view(*v)),
          CMessage::Redirect{ k, id } => valid_key(*k) && id@.valid_physical_address(),
          CMessage::Shard{ kr, recipient } => recipient@.valid_physical_address() && !kr.is_empty(),
          CMessage::Delegate{ range, h } => !range.is_empty() && valid_hashtable(h@),
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


pub open spec fn cpacket_seq_is_abstractable(packets: Seq<CPacket>) -> bool
{
    forall |i: int| 0 <= i && i < packets.len() ==> #[trigger] packets[i].abstractable()
}

pub open spec fn abstractify_outbound_packets_to_seq_of_lsht_packets(packets: Seq<CPacket>) -> Seq<LSHTPacket>
  recommends cpacket_seq_is_abstractable(packets)
{
  packets.map_values(|packet: CPacket| abstractify_cpacket_to_lsht_packet(packet))
}

pub open spec fn abstractify_seq_of_cpackets_to_set_of_sht_packets(cps: Seq<CPacket>) -> Set<Packet>
    recommends cpacket_seq_is_abstractable(cps)
{
    cps.map_values(|cp: CPacket| cp@).to_set()
}


// File: marshal_v.rs
pub trait Marshalable : Sized {

  spec fn is_marshalable(&self) -> bool;

	#[verifier::external_body]
  spec fn ghost_serialize(&self) -> Seq<u8>
    recommends self.is_marshalable()
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
impl Ordering {

    pub open spec fn lt(self) -> bool {
        matches!(self, Ordering::Less)
    }

}


#[verifier::reject_recursive_types(K)]
pub struct DelegationMap<K: KeyTrait + VerusClone> {
    // Our efficient implementation based on ranges
    lows: StrictlyOrderedMap<K>,
    // Our spec version
    m: Ghost<Map<K, AbstractEndPoint>>,

}

impl<K: KeyTrait + VerusClone> DelegationMap<K> {

	#[verifier::external_body]
    pub closed spec fn view(self) -> Map<K,AbstractEndPoint>
	{
		unimplemented!()
	}

	#[verifier::external_body]
    pub closed spec fn valid(self) -> bool
	{
		unimplemented!()
	}

	#[verifier::external_body]
    pub fn get(&self, k: &K) -> (id: ID)
        requires
            self.valid(),
        ensures
            id@ == self@[*k],
            id@.valid_physical_address(),
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


pub open spec fn abstractify_cpacket_to_lsht_packet(cp: CPacket) -> LSHTPacket
  recommends cp.abstractable()
{
  LPacket{ dst: cp.dst@, src: cp.src@, msg: cp.msg@ }
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

    pub closed spec fn host_state_packet_preconditions(&self, cpacket: CPacket) -> bool
    {
        &&& self.abstractable()
        &&& cpacket.abstractable()
        &&& self.valid()
        &&& cpacket.src@.valid_physical_address()
        &&& self.constants.params@ == AbstractParameters::static_params()
        &&& self.resend_count < 100000000
    }

    pub closed spec fn host_state_common_preconditions(&self) -> bool
    {
        match self.received_packet {
            Some(cpacket) => self.host_state_packet_preconditions(cpacket),
            None => false,
        }
    }

    pub closed spec fn next_get_request_preconditions(&self) -> bool
    {
        &&& self.abstractable()
        &&& self.received_packet is Some
        &&& { let cpacket = self.received_packet.unwrap();
            { &&& cpacket.abstractable()
              &&& cpacket.msg is Message
              &&& cpacket.msg.arrow_Message_m() is GetRequest
              &&& cpacket.src@.valid_physical_address()
            } }
        &&& self.sd.valid()
        &&& self.host_state_common_preconditions()
    }

    pub closed spec fn next_get_request_postconditions(&self, pre: Self, sent_packets: Seq<CPacket>) -> bool
    {
        &&& pre.next_get_request_preconditions()
        &&& self.abstractable()
        &&& cpacket_seq_is_abstractable(sent_packets)
        &&& match pre.received_packet {
                Some(cpacket) => next_get_request(pre@, self@, cpacket@,
                                                 abstractify_seq_of_cpackets_to_set_of_sht_packets(sent_packets)),
                None => false,
            }
        &&& self.host_state_common_postconditions(pre, pre.received_packet.unwrap(), sent_packets)
        &&& self.received_packet is None
    }

    pub closed spec fn host_state_common_postconditions(
        &self,
        pre: Self,
        cpacket: CPacket,
        sent_packets: Seq<CPacket>
    ) -> bool
    {
// Removed at Lorch's suggestion: In Dafny, we needed this line to satisfy requires for later
// terms; in Verus we don't because we're living carelessly wrt recommends.
// Since we've split off host_state_common_preconditions for the receive_packet case (due to
// not being able to duplicate exec cpacket), we're trying to avoid propagating that change here.
//         &&& pre.host_state_common_preconditions()
        &&& self.abstractable()
        &&& self.constants == pre.constants
        &&& cpacket_seq_is_abstractable(sent_packets)
        &&& self.valid()
        &&& self.next_action_index == pre.next_action_index
        &&& outbound_packet_seq_is_valid(sent_packets)
        &&& outbound_packet_seq_has_correct_srcs(sent_packets, pre.constants.me@)
        &&& (forall |i: int| 0 <= i && i < sent_packets.len() ==>
              (#[trigger] sent_packets[i].msg) is Message || sent_packets[i].msg is Ack)
        &&& abstractify_seq_of_cpackets_to_set_of_sht_packets(sent_packets) =~=
            extract_packets_from_lsht_packets(abstractify_outbound_packets_to_seq_of_lsht_packets(sent_packets))
        &&& self.resend_count < 100000000
    }

    fn host_model_next_get_request(&mut self) -> (sent_packets: Vec<CPacket>)
        requires old(self).next_get_request_preconditions()
        ensures  self.next_get_request_postconditions(*old(self), sent_packets@)
    {
        let cpacket: &CPacket = &self.received_packet.as_ref().unwrap();
        let ghost pkt: Packet = cpacket@;
        match &cpacket.msg {
            CSingleMessage::Message{m: CMessage::GetRequest{k}, seqno, ..} => {
                let owner: EndPoint = self.delegation_map.get(k);
                let ghost received_request: AppRequest = AppRequest::AppGetRequest{seqno: seqno@ as nat, key: *k};
                let its_me: bool = do_end_points_match(&owner, &self.constants.me);
                let m: CMessage =
                    if its_me {
                        let v = self.h.get(k);
                        // OBSERVE: Need to say `valid_value` to trigger the quantifier saying all values are valid.
                        assert (v.is_some() ==> valid_value(v.arrow_Some_0()@));
                        CMessage::Reply{k: SHTKey{ukey: k.ukey}, v: clone_option_vec_u8(v)}
                    }
                    else {
                        CMessage::Redirect{k: SHTKey{ukey: k.ukey}, id: clone_end_point(&owner)}
                    };
                let ghost new_received_requests: Seq<AppRequest> =
                    if its_me {
                        self.received_requests@.push(received_request)
                    }
                    else {
                        self.received_requests@
                    };
                proof { lemma_auto_spec_u64_to_from_le_bytes(); }
                assert (m.is_marshalable());
                let optional_sm = self.sd.send_single_cmessage(&m, &cpacket.src);
                let mut sent_packets = Vec::<CPacket>::new();
                match optional_sm {
                    Some(sm) => {
                        let p = CPacket{
                            dst: clone_end_point(&cpacket.src),
                            src: clone_end_point(&self.constants.me),
                            msg: sm
                        };
                        self.received_requests = Ghost(new_received_requests);
                        self.received_packet = None;
                        sent_packets.push(p);
                        // TODO replace a bunch of the proof below with these lines:
//                         proof {
//                             lemma_map_values_singleton_auto::<CPacket, Packet>();
//                             to_set_singleton_auto::<Packet>();
//                         }
                        proof {
                            let ap = abstractify_cpacket_to_lsht_packet(p);
                            let bp = Packet{dst: ap.dst, src: ap.src, msg: ap.msg};
                            assert_seqs_equal!(Seq::<CPacket>::empty().push(p).map_values(|cp: CPacket| cp@),
                                               Seq::<Packet>::empty().push(p@));
                            assert (Seq::<Packet>::empty().push(p@).index(0) == p@); // needed to show it contains p@
                            assert_sets_equal!(abstractify_seq_of_cpackets_to_set_of_sht_packets(sent_packets@),
                                               Seq::<CPacket>::empty().push(p).map_values(|cp: CPacket| cp@).to_set());
                            assert_sets_equal!(abstractify_seq_of_cpackets_to_set_of_sht_packets(sent_packets@),
                                               Set::<Packet>::empty().insert(p@));
                            assert_sets_equal!(abstractify_seq_of_cpackets_to_set_of_sht_packets(sent_packets@),
                                               set![ Packet{dst: pkt.src, src: self.constants.me@, msg: sm@} ]);
                            assert_seqs_equal!(abstractify_outbound_packets_to_seq_of_lsht_packets(sent_packets@),
                                               Seq::<LSHTPacket>::empty().push(ap));
                            assert_seqs_equal!(abstractify_outbound_packets_to_seq_of_lsht_packets(sent_packets@)
                                               .map_values(|lp: LSHTPacket| extract_packet_from_lsht_packet(lp)),
                                               Seq::<Packet>::empty().push(bp));
                            assert (Seq::<Packet>::empty().push(bp).index(0) == bp); // needed to show it contains bp
                            assert_sets_equal!(Seq::<Packet>::empty().push(bp).to_set(),
                                               Set::<Packet>::empty().insert(bp));
                            assert (next_get_request_reply(
                                        old(self)@, self@, pkt.src, pkt.msg.arrow_Message_seqno(),
                                        pkt.msg.arrow_Message_m().arrow_GetRequest_key(),
                                        sm@, m@,
                                        abstractify_seq_of_cpackets_to_set_of_sht_packets(sent_packets@),
                                        true));
                        }
                        return sent_packets;
                    },
                    None => {
                        self.received_packet = None;
                        proof {
                            assert( sent_packets@ =~= Seq::<CPacket>::empty() );
                            assert( abstractify_seq_of_cpackets_to_set_of_sht_packets(sent_packets@) =~= Set::<Packet>::empty() );
                            assert (next_get_request_reply(
                                        old(self)@, self@, pkt.src, pkt.msg.arrow_Message_seqno(),
                                        pkt.msg.arrow_Message_m().arrow_GetRequest_key(),
                                        SingleMessage::<Message>::InvalidMessage{}, m@,
                                        abstractify_seq_of_cpackets_to_set_of_sht_packets(sent_packets@),
                                        false));
                            assert_sets_equal!(abstractify_seq_of_cpackets_to_set_of_sht_packets(sent_packets@),
                                               extract_packets_from_lsht_packets(
                                                   abstractify_outbound_packets_to_seq_of_lsht_packets(sent_packets@)));
                        }
                        return sent_packets;
                    }
                }
            },
            _ => {
                assert(false);
                unreached()
            },
        }
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

    #[verifier(inline)]
    pub open spec fn view(self) -> Map<AbstractKey, AbstractEndPoint> {
        self.0
    }

    #[verifier(inline)]
    pub open spec fn spec_index(self, key: AbstractKey) -> AbstractEndPoint
        recommends self.0.dom().contains(key)
    {
        self@.index(key)
    }

    pub open spec fn is_complete(self) -> bool {
        self@.dom().is_full()
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


// File: environment_t.rs
pub struct LPacket<IdType, MessageType> {
    pub dst: IdType,
    pub src: IdType,
    pub msg: MessageType,
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
    pub fn get(&self, key: &CKey) -> (value: Option<&Vec<u8>>)
      ensures (match value {
        Some(v) => self@.dom().contains(*key) && self@[*key] == v@,
        None => !self@.dom().contains(*key),
    })
	{
		unimplemented!()
	}

    pub uninterp spec fn spec_to_vec(&self) -> Vec<CKeyKV>;
    #[verifier(external_body)]
    #[verifier(when_used_as_spec(spec_to_vec))]
    pub fn to_vec(&self) -> (res: Vec<CKeyKV>) 
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

pub open spec fn max_hashtable_size() -> int
{
    62
}

pub open spec fn valid_hashtable(h: Hashtable) -> bool
{
    &&& h.dom().len() < max_hashtable_size()
    &&& (forall |k| h.dom().contains(k) ==> valid_key(k) && #[trigger] valid_value(h[k]))
}

pub open spec(checked) fn hashtable_lookup(h: Hashtable, k: AbstractKey) -> Option<AbstractValue>
{
    if h.dom().contains(k) { Some(h[k]) } else { None }
}

pub open spec(checked) fn valid_optional_value(ov: Option<AbstractValue>) -> bool
{
    match ov {
        None => true,
        Some(value) => valid_value(value),
    }
}

pub open spec fn extract_packet_from_lsht_packet(lp: LSHTPacket) -> Packet
{
    Packet { dst: lp.dst, src: lp.src, msg: lp.msg }
}

pub open spec fn extract_packets_from_lsht_packets(seq_packets: Seq<LSHTPacket>) -> Set<Packet>
{
  seq_packets.map_values(|lp: LSHTPacket| extract_packet_from_lsht_packet(lp)).to_set()
}

pub open spec(checked) fn next_get_request_reply(pre: AbstractHostState, post: AbstractHostState, src: AbstractEndPoint, seqno: nat, k: AbstractKey, sm: SingleMessage<Message>, m: Message, out: Set<Packet>, should_send: bool) -> bool
    recommends pre.delegation_map.is_complete()
{
    let owner = pre.delegation_map[k];
    if should_send && valid_key(k) {
        &&& if owner == pre.constants.me {
                &&& m == Message::Reply{key: k, value: hashtable_lookup(pre.h, k)}
                &&& post.received_requests == pre.received_requests.push(AppRequest::AppGetRequest{seqno, key: k})
            } else {
                &&& m == Message::Redirect{key: k, id: owner}
                &&& post.received_requests == pre.received_requests
            }
        &&& SingleDelivery::send_single_message(pre.sd, post.sd, m, src, Some(sm), pre.constants.params)
        &&& sm.arrow_Message_dst() == src
        &&& out == set![ Packet{dst: src, src: pre.constants.me, msg: sm} ]
    } else {
        &&& post == AbstractHostState { received_packet: post.received_packet, ..pre }
        &&& out == Set::<Packet>::empty()
    }
}

pub open spec(checked) fn next_get_request(pre: AbstractHostState, post: AbstractHostState, pkt: Packet, out: Set<Packet>) -> bool
    recommends
        pkt.msg is Message,
        pre.delegation_map.is_complete(),
{
    &&& pkt.msg.arrow_Message_m() is GetRequest
    &&& post.delegation_map == pre.delegation_map
    &&& post.h == pre.h
    &&& post.num_delegations == pre.num_delegations
    &&& (exists |sm,m,b| next_get_request_reply(pre, post, pkt.src, pkt.msg.arrow_Message_seqno(), pkt.msg.arrow_Message_m().arrow_GetRequest_key(), sm, m, out, b))
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

    #[verifier(inline)]
    pub open spec fn abstractable(self) -> bool {
        self@.valid_physical_address()
    }

}


pub open spec fn abstractify_end_points(end_points: Vec<EndPoint>) -> Seq<AbstractEndPoint>
{
    end_points@.map(|i, end_point: EndPoint| end_point@)
}


// File: keys_t.rs
pub trait KeyTrait : Sized {

    spec fn cmp_spec(self, other: Self) -> Ordering;

}


#[derive(Structural, PartialEq, Eq)]
pub enum Ordering {
    Less,
    Equal,
    Greater,
}

pub struct KeyIterator<K: KeyTrait + VerusClone> {
    // None means we hit the end
    pub k: Option<K>,
}

impl<K: KeyTrait + VerusClone> KeyIterator<K> {

    pub open spec fn lt_spec(self, other: Self) -> bool {
        (!self.k.is_None() && other.k.is_None())
      || (!self.k.is_None() && !other.k.is_None() && self.k.get_Some_0().cmp_spec(other.k.get_Some_0()).lt())
    }

    pub open spec fn geq_spec(self, other: Self) -> bool {
        !self.lt_spec(other) //|| self == other
    }

}


pub struct KeyRange<K: KeyTrait + VerusClone> {
    pub lo: KeyIterator<K>,
    pub hi: KeyIterator<K>,
}

impl<K: KeyTrait + VerusClone> KeyRange<K> {

    pub open spec fn is_empty(self) -> bool
    {
        self.lo.geq_spec(self.hi)
    }

}


#[derive(Eq,PartialEq,Hash)]
pub struct SHTKey {
    pub // workaround
        ukey: u64,
}

impl KeyTrait for SHTKey {

    open spec fn cmp_spec(self, other: Self) -> Ordering
    {
        if self.ukey < other.ukey {
            Ordering::Less
        } else if self.ukey == other.ukey {
            Ordering::Equal
        } else {
            Ordering::Greater
        }
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

pub open spec(checked) fn ack_state_lookup<MT>(src: AbstractEndPoint, send_state: SendState<MT>) -> AckState<MT> {
    if send_state.contains_key(src)
        { send_state[src] }
    else
        { AckState{num_packets_acked: 0, un_acked: Seq::empty()} }
}

#[verifier::ext_equal]
pub struct SingleDelivery<MT> {
    pub receive_state: TombstoneTable,
    pub send_state: SendState<MT>
}

impl<MT> SingleDelivery<MT> {

    pub open spec(checked) fn send_single_message(pre: Self, post: Self, m: MT, dst: AbstractEndPoint, /*out*/ sm: Option<SingleMessage<MT>>, params: AbstractParameters) -> bool
    {
        let old_ack_state = ack_state_lookup(dst, pre.send_state);
        let new_seqno = old_ack_state.num_packets_acked + old_ack_state.un_acked.len() + 1;
        if new_seqno > params.max_seqno {
            // Packet shouldn't be sent if we exceed the maximum sequence number
            &&& post == pre
            &&& sm is None
        } else {
            &&& sm == Some(SingleMessage::<MT>::Message{
                    seqno: new_seqno,
                    m: m,
                    dst: dst,
                })
            &&& post == SingleDelivery {
                send_state: pre.send_state.insert(dst,
                    AckState{
                        un_acked: old_ack_state.un_acked.push(sm.unwrap()),
                        ..old_ack_state }),
                ..pre }
        }
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


// File: net_sht_v.rs
pub open spec fn outbound_packet_is_valid(cpacket: &CPacket) -> bool
{
    &&& cpacket.abstractable()  // CPacketIsAbstractable
    &&& cpacket.msg.is_marshalable()   // CSingleMessageMarshallable
    &&& !(cpacket.msg is InvalidMessage) // (out.msg.CSingleMessage? || out.msg.CAck?)
}

pub open spec fn outbound_packet_seq_is_valid(cpackets: Seq<CPacket>) -> bool
{
    forall |i| 0 <= i < cpackets.len() ==> #[trigger] outbound_packet_is_valid(&cpackets[i])
}

pub open spec fn outbound_packet_seq_has_correct_srcs(cpackets: Seq<CPacket>, end_point: AbstractEndPoint) -> bool
{
    forall |i| #![auto] 0 <= i < cpackets.len() ==> cpackets[i].src@ == end_point
}


// File: seq_is_unique_v.rs
	#[verifier::opaque]
    pub open spec fn seq_is_unique<T>(s: Seq<T>) -> bool
    {
        forall |i: int, j: int| #![trigger s[i], s[j]] 0 <= i && i < s.len() && 0 <= j && j < s.len() && s[i] == s[j] ==> i == j
    }

	#[verifier::external_body]
    pub fn do_end_points_match(e1: &EndPoint, e2: &EndPoint) -> (eq: bool)
        ensures
            eq == (e1@ == e2@)
	{
		unimplemented!()
	}

	#[verifier::external_body]
    pub fn clone_option_vec_u8(ov: Option<&Vec<u8>>) -> (res: Option<Vec<u8>>)
        ensures
            match ov {
                Some(e1) => res.is_some() && e1@ == res.get_Some_0()@,
                None => res.is_None(),
            }
	{
		unimplemented!()
	}

	#[verifier::external_body]
    pub fn clone_end_point(ep: &EndPoint) -> (cloned_ep: EndPoint)
        ensures
            cloned_ep@ == ep@
	{
		unimplemented!()
	}


// File: single_delivery_model_v.rs
impl CSingleDelivery {

	#[verifier::external_body]
    #[verifier::rlimit(15)]
    pub fn send_single_cmessage(&mut self, m: &CMessage, dst: &EndPoint) -> (sm: Option<CSingleMessage>)
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
                    &&& SingleDelivery::send_single_message(old(self)@, self@, m@, dst@, Some(sm@), AbstractParameters::static_params())
                    &&& sm.is_marshalable()
                },
                None =>
                    SingleDelivery::send_single_message(old(self)@, self@, m@, dst@, None, AbstractParameters::static_params()),
            }
	{
		unimplemented!()
	}

}


// File: app_interface_t.rs
pub open spec fn max_val_len() -> int { 1024 }

pub open spec fn valid_key(key: AbstractKey) -> bool { true }

pub open spec fn valid_value(value: AbstractValue) -> bool { value.len() < max_val_len() }


pub trait VerusClone {}

impl VerusClone for SHTKey {}

////////////////
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


}
