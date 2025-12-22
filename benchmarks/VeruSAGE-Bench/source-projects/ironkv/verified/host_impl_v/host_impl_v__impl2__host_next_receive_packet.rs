extern crate verus_builtin_macros as builtin_macros;
use vstd::prelude::*;
use std::collections;
use vstd::bytes::*;
use std::time::SystemTime;

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
    pub proof fn valid_implies_complete(&self)
        requires self.valid()
        ensures  self@.dom().is_full()
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


pub open spec fn all_ios_are_sends(ios: Seq<LSHTIo>) -> bool
{
    forall |i: int| 0 <= i && i < ios.len() ==> ios[i] is Send
}

pub open spec fn abstractify_cpacket_to_lsht_packet(cp: CPacket) -> LSHTPacket
  recommends cp.abstractable()
{
  LPacket{ dst: cp.dst@, src: cp.src@, msg: cp.msg@ }
}

pub open spec fn map_sent_packet_seq_to_ios(sent_packets: Seq<CPacket>) -> Seq<LSHTIo>
{
  sent_packets.map_values(|sent_packet: CPacket|
                   LIoOp::<AbstractEndPoint, SingleMessage<Message>>::Send {
                       s: abstractify_cpacket_to_lsht_packet(sent_packet)
                   })
}

pub open spec fn abstractify_raw_log_to_ios(rawlog: Seq<NetEvent>) -> Seq<LSHTIo>
{
  rawlog.map_values(|evt: NetEvent| abstractify_net_event_to_lsht_io(evt))
}

pub open spec fn raw_io_consistent_with_spec_io(rawlog: Seq<NetEvent>, ios: Seq<LSHTIo>) -> bool
{
    &&& net_event_log_is_abstractable(rawlog)
    &&& abstractify_raw_log_to_ios(rawlog) == ios
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
    pub fn deliver_outbound_packets(&self, netc: &mut NetClient, packets: &Vec<CPacket>) ->
        (rc: (bool, Ghost<Seq<NetEvent>>, Ghost<Seq<LSHTIo>>))
        requires
            old(netc).ok(),
            outbound_packet_seq_is_valid(packets@),
            outbound_packet_seq_has_correct_srcs(packets@, old(netc).my_end_point()),
        ensures
            netc.my_end_point() == old(netc).my_end_point(),
            ({
                let (ok, Ghost(net_events), Ghost(ios)) = rc;
                {
                    &&& netc.ok() <==> ok
                    &&& ok ==> {
                        &&& all_ios_are_sends(ios)
                        &&& (forall |i: int| 0 <= i && i < net_events.len() ==> net_events[i] is Send)
                        &&& ios == map_sent_packet_seq_to_ios(packets@)
                        &&& abstractify_outbound_packets_to_seq_of_lsht_packets(packets@) ==
                                extract_sent_packets_from_ios(ios)
                        &&& abstractify_seq_of_cpackets_to_set_of_sht_packets(packets@) ==
                                extract_packets_from_abstract_ios(ios)
                        &&& no_invalid_sends(ios)
                        &&& raw_io_consistent_with_spec_io(net_events, ios)
                        &&& only_sent_marshalable_data(net_events)
                        &&& netc.history() == old(netc).history() + net_events
                    }
                }
            })
	{
		unimplemented!()
	}

	#[verifier::external_body]
    proof fn empty_event_results() -> (event_results: EventResults)
    ensures
        event_results.well_typed_events(),
        event_results.ios =~= event_results.event_seq(),
        event_results.ios == Seq::<NetEvent>::empty(),
	{
		unimplemented!()
	}

    #[verifier(spinoff_prover)] // suddenly this is taking a long time due to an unrelated change elsewhere
    fn host_next_receive_packet(
        &mut self,
        netc: &mut NetClient,
        Ghost(old_netc_history): Ghost<Seq<NetEvent>>,
        cpacket: CPacket,
        Ghost(receive_event): Ghost<NetEvent>
    ) -> (rc: (bool, Ghost<EventResults>, Ghost<Seq<LSHTIo>>))
    requires
        old(netc).ok(),
        old(self).invariants(&old(netc).my_end_point()),
        !(cpacket.msg is InvalidMessage),
        cpacket.dst@ == old(self).constants.me@,
        // cpacket.dst@ == old(netc).my_end_point(),    // probably provable from the above
        cpacket.abstractable(),
        cpacket.src@.valid_physical_address(),
        old(netc).history() == old_netc_history.push(receive_event),
        receive_event is Receive,
        abstractify_cpacket_to_lsht_packet(cpacket) == abstractify_net_packet_to_lsht_packet(receive_event.arrow_Receive_r()),
    ensures ({
        let (ok, Ghost(event_results), Ghost(ios)) = rc;
        &&& self.invariants(&netc.my_end_point())
        &&& self@.constants == old(self)@.constants
        &&& ok == netc.ok()
        // Because all `net_events` are sends, the condition "even if ok is false, if we sent at least one
        // packet..." is implied by "even if ok is false, if `net_events` has length > 0...".
        &&& (ok || event_results.sends.len() > 0) ==> netc.history() == old_netc_history + event_results.ios
        // There's supposed to be a distinction between the ios that we intended to do and the
        // event_seq that we actually did. (See EventResult definition.) But in the interest of
        // mimicking Dafny Ironfleet, we make no such distinction.
        &&& event_results.ios == event_results.event_seq()
        &&& event_results.well_typed_events()
        &&& ok ==> {
            &&& receive_packet_next(old(self)@, self@, ios)
            &&& raw_io_consistent_with_spec_io(event_results.ios, ios)
            &&& no_invalid_sends(ios)
            }
        }),
    {
        let (sent_packets, ack) = self.host_model_receive_packet(cpacket);
        let ghost io0 = LIoOp::Receive{ r: abstractify_cpacket_to_lsht_packet(cpacket) };
        let ghost ios_head = seq![io0];
        proof {
            let sent_packets_v = abstractify_seq_of_cpackets_to_set_of_sht_packets(sent_packets@);
            let mapped = sent_packets@.map_values(|cp: CPacket| cp@);
            let setted = mapped.to_set();
            if 0 < sent_packets_v.len() {

                // TODO(verus): improve automation for .map and .to_set. Note here we need lots of
                // triggering.
                assert forall |i| #![auto] 0 <= i < sent_packets@.len()
                    implies sent_packets@[i].src@ == netc.my_end_point() by {
                    let cpacket = sent_packets@[i];
                    assert( mapped[i] == cpacket@ );        // witness
                    assert( setted.contains(cpacket@) );    // trigger
                }
            } else {
                assert( 0 == mapped.len() ) by {
                    if 0 < mapped.len() {
                        assert( setted.contains(mapped[0]) );   // witness
                    }
                }
            }
            assert( outbound_packet_seq_has_correct_srcs(sent_packets@, netc.my_end_point()) );
        }
        assert(netc.history() == old(netc).history());
        let rc = self.deliver_outbound_packets(netc, &sent_packets);

        let (ok, Ghost(net_events), Ghost(ios_tail)) = rc;
        assert( ok == netc.ok() );
        if !ok {
            proof {
                self.delegation_map.valid_implies_complete();   // sorry, valid is opaque now
            }
            let ghost event_results = Self::empty_event_results();
            return (false, Ghost(event_results), Ghost(Seq::<LSHTIo>::empty()));
        }

        let ghost ios = ios_head + ios_tail;
        proof {
            old(self).delegation_map.valid_implies_complete();  // sorry, valid is opaque now
        }
        assert(ios_tail =~= ios.skip(1));
        proof {
            lemma_filter_skip_rejected(ios, |io: LSHTIo| io is Send, 1);
        }
        assert(receive_packet(old(self)@, self@, cpacket@, extract_packets_from_abstract_ios(ios), ack@@)); // trigger

        let ghost event_results = EventResults{
            recvs: seq![receive_event],
            clocks: seq![],
            sends: net_events,
            ios: seq![receive_event] + net_events,
        };
        assert(abstractify_raw_log_to_ios(event_results.ios) =~= ios); // extensional equality

        proof {
            self.delegation_map.valid_implies_complete();   // sorry, valid is opaque now
            assert( netc.history() =~= old_netc_history + event_results.ios );
            assert(event_results.ios == event_results.event_seq());
        }
        (ok, Ghost(event_results), Ghost(ios))
    }

	#[verifier::external_body]
    fn host_model_receive_packet(&mut self, cpacket: CPacket) -> (rc: (Vec<CPacket>, Ghost<CPacket>))
    requires
        old(self).valid(),
        old(self).host_state_packet_preconditions(cpacket),
        !(cpacket.msg is InvalidMessage),
        cpacket.dst@ == old(self).constants.me@,
    ensures ({
        let (sent_packets, ack) = rc;
        &&& outbound_packet_seq_is_valid(sent_packets@)
        &&& receive_packet(old(self)@, self@, cpacket@, abstractify_seq_of_cpackets_to_set_of_sht_packets(sent_packets@), ack@@)
        // The Dafny Ironfleet "common preconditions" take an explicit cpacket, but we need to talk
        // about
        &&& self.host_state_common_postconditions(*old(self), cpacket, sent_packets@)

    })	{
		unimplemented!()
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

impl EventResults {

    pub open spec fn event_seq(self) -> Seq<NetEvent> {
        self.recvs + self.clocks + self.sends
    }

    pub open spec fn well_typed_events(self) -> bool {
        &&& forall |i| 0 <= i < self.recvs.len() ==> self.recvs[i] is Receive
        &&& forall |i| 0 <= i < self.clocks.len() ==> self.clocks[i] is ReadClock || self.clocks[i] is TimeoutReceive
        &&& forall |i| 0 <= i < self.sends.len() ==> self.sends[i] is Send
        &&& self.clocks.len() <= 1
    }

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

	#[verifier::external_body]
pub open spec fn okay_to_ignore_packets() -> bool {
		unimplemented!()
	}


pub open spec(checked) fn receive_packet(pre: AbstractHostState, post: AbstractHostState, pkt: Packet, out: Set<Packet>, ack: Packet) -> bool {
    ||| {
           &&& pre.received_packet is None // No packet currently waiting to be processed (buffered in my state)
            // Record incoming packet in my state and possibly ack it
           &&& SingleDelivery::receive(pre.sd, post.sd, pkt, ack, out)
           &&& if SingleDelivery::new_single_message(pre.sd, pkt) {
                   post.received_packet == Some(pkt)   // Enqueue this packet for processing
              } else {
                  post.received_packet is None
              }
           &&& post == AbstractHostState {sd: post.sd, received_packet: post.received_packet, ..post} // Nothing else changes
       }
    ||| {
           // internal buffer full or okay to ignore packets; drop this message and wait for it to be retransmitted.
           &&& pre.received_packet is Some || okay_to_ignore_packets()
           &&& post == pre
           &&& out == Set::<Packet>::empty()
       }
}

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

pub open spec(checked) fn receive_packet_wrapper(pre: AbstractHostState, post: AbstractHostState, pkt: Packet, sent_packets: Set<Packet>) -> bool
{
    exists |ack| receive_packet(pre, post, pkt, sent_packets, ack)
}

pub open spec(checked) fn receive_packet_without_reading_clock(pre: AbstractHostState, post: AbstractHostState, ios: AbstractIos) -> bool
recommends
    ios.len() >= 1,
    ios[0] is Receive,
    pre.delegation_map.is_complete(),
{
    let r = ios[0].arrow_Receive_r();
    let pkt = Packet{dst: r.dst, src: r.src, msg: r.msg};
    let sent_packets = extract_packets_from_abstract_ios(ios);
    receive_packet_wrapper(pre, post, pkt, sent_packets)
}

pub open spec(checked) fn receive_packet_next(pre: AbstractHostState, post: AbstractHostState, ios: AbstractIos) -> bool {
    &&& ios.len() >= 1
    &&& if ios[0] is TimeoutReceive {
            &&& post == pre
            &&& ios.len() == 1
        } else  {
            &&& pre.delegation_map.is_complete()
            &&& ios[0] is Receive
            &&& forall |i| 1 <= i < ios.len() ==> /*#[trigger]*/ ios[i] is Send
            &&& receive_packet_without_reading_clock(pre, post, ios)
        }
}

pub open spec(checked) fn no_invalid_sends(ios: AbstractIos) -> bool {
    forall |i| #![auto] 0 <= i < ios.len() && ios[i] is Send ==> !(ios[i].arrow_Send_s().msg is InvalidMessage)
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

	#[verifier::external_body]
    pub closed spec fn history(&self) -> History
	{
		unimplemented!()
	}

	#[verifier::external_body]
    pub closed spec fn my_end_point(&self) -> AbstractEndPoint
	{
		unimplemented!()
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


// File: single_delivery_t.rs
pub open spec fn tombstone_table_lookup(src: AbstractEndPoint, t: TombstoneTable) -> nat
{
    if t.dom().contains(src) { t[src] } else { 0 }
}

pub open spec(checked) fn truncate_un_ack_list<MT>(un_acked: AckList<MT>, seqno_acked: nat) -> Seq<SingleMessage<MT>>
decreases un_acked.len()
{
    if un_acked.len() > 0 && un_acked[0] is Message && un_acked[0].arrow_Message_seqno() <= seqno_acked {
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

    pub open spec(checked) fn new_single_message(self, pkt: Packet) -> bool {
        let last_seqno = tombstone_table_lookup(pkt.src, self.receive_state);
        &&& pkt.msg is Message
        &&& pkt.msg.arrow_Message_seqno() == last_seqno + 1
    }

    pub open spec(checked) fn receive_ack(pre: Self, post: Self, pkt: Packet, acks:Set<Packet>) -> bool
    recommends
        pkt.msg is Ack,
    {
        &&& acks.is_empty()
        &&& {
            let old_ack_state = ack_state_lookup(pkt.src, pre.send_state);
            if pkt.msg.arrow_Ack_ack_seqno() > old_ack_state.num_packets_acked {
                let new_ack_state = AckState{
                        num_packets_acked: pkt.msg.arrow_Ack_ack_seqno(),
                        un_acked: truncate_un_ack_list(old_ack_state.un_acked, pkt.msg.arrow_Ack_ack_seqno()),
                        .. old_ack_state};
                post =~= Self{ send_state: pre.send_state.insert(pkt.src, new_ack_state), ..post }
            } else {
                post == pre
            }
        }
    }

    pub open spec(checked) fn receive_real_packet(self, post: Self, pkt: Packet) -> bool {
        if self.new_single_message(pkt) {
            let last_seqno = tombstone_table_lookup(pkt.src, self.receive_state);
            // Mark it received
            post == Self{ receive_state: self.receive_state.insert(pkt.src, (last_seqno + 1) as nat), ..self }
        } else {
            post == self
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

    pub open spec(checked) fn maybe_ack_packet(pre: Self, pkt: Packet, ack: Packet, acks:Set<Packet>) -> bool {
        if pre.should_ack_single_message(pkt) {
            pre.send_ack(pkt, ack, acks)
        } else {
            acks.is_empty()
        }
    }

    pub open spec(checked) fn receive(pre: Self, post: Self, pkt: Packet, ack: Packet, acks:Set<Packet>) -> bool {
        match pkt.msg {
            SingleMessage::Ack{ack_seqno: _} => Self::receive_ack(pre, post, pkt, acks),
            SingleMessage::Message{seqno, dst: _, m} => {
                &&& Self::receive_real_packet(pre, post, pkt)
                &&& Self::maybe_ack_packet(post, pkt, ack, acks)
            }
            SingleMessage::InvalidMessage{} => {
                &&& post === pre
                &&& acks === Set::empty()
            }
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


// File: verus_extra/seq_lib_v.rs
	#[verifier::external_body]
pub proof fn lemma_filter_skip_rejected<A>(s: Seq<A>, pred: spec_fn(A) -> bool, i: int)
    requires
        0 <= i <= s.len(),
        forall |j| 0 <= j < i ==> !pred(s[j]),
    ensures
        s.filter(pred) == s.skip(i).filter(pred)
    decreases
        s.len()
	{
		unimplemented!()
	}


// File: marshal_ironsht_specific_v.rs
	#[verifier::external_body]
    pub open spec fn ckeyhashmap_max_serialized_size() -> usize {
		unimplemented!()
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

pub open spec fn net_event_log_is_abstractable(rawlog: Seq<NetEvent>) -> bool
{
    forall |i: int| 0 <= i && i < rawlog.len() ==> #[trigger] net_event_is_abstractable(rawlog[i])
}

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

pub open spec fn net_packet_bound(data: Seq<u8>) -> bool
{
    data.len() <= 0xffff_ffff_ffff_ffff
}

pub open spec fn is_marshalable_data(event: NetEvent) -> bool
    recommends event is Send
{
    &&& net_packet_bound(event.arrow_Send_s().msg)
    &&& sht_demarshal_data(event.arrow_Send_s().msg).is_marshalable()
}

pub open spec fn only_sent_marshalable_data(rawlog:Seq<NetEvent>) -> bool
{
    forall |i| 0 <= i < rawlog.len() && rawlog[i] is Send ==>
        #[trigger] is_marshalable_data(rawlog[i])
}


// File: seq_is_unique_v.rs
	#[verifier::external_body]
    pub open spec fn seq_is_unique<T>(s: Seq<T>) -> bool
	{
		unimplemented!()
	}


// File: app_interface_t.rs
pub open spec fn max_val_len() -> int { 1024 }

pub open spec fn valid_value(value: AbstractValue) -> bool { value.len() < max_val_len() }


pub trait KeyTrait {}

pub trait VerusClone {}

impl VerusClone for SHTKey {}


impl KeyTrait for SHTKey {}

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
pub type History = Seq<NetEvent>;
pub type NetPacket = LPacket<AbstractEndPoint, Seq<u8>>;
pub type AbstractIos = Seq<LSHTIo>;
pub type LSHTIo = LIoOp<AbstractEndPoint, SingleMessage<Message>>;
type Ios = Seq<NetEvent>;
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
    event_counter: std::collections::HashMap<std::string::String, u64>,
}


}
