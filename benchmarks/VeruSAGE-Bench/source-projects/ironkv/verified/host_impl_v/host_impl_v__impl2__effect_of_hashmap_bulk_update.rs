extern crate verus_builtin_macros as builtin_macros;
use vstd::map::*;
use vstd::seq::*;
use vstd::set::*;
use std::collections;
use vstd::prelude::*;

fn main(){}

verus! {

pub trait VerusClone {}

    /*****abstract_service_t.rs*/
pub enum AppRequest {
    AppGetRequest{seqno:nat, key:AbstractKey},
    AppSetRequest{seqno:nat, key:AbstractKey, ov:Option<AbstractValue>},
}


/*app_interface_t*/
pub open spec fn max_val_len() -> int { 1024 }

pub open spec fn valid_key(key: AbstractKey) -> bool { true }

pub open spec fn valid_value(value: AbstractValue) -> bool { value.len() < max_val_len() }

/*cmesssage_v.rs*/

#[allow(inconsistent_fields)]
pub enum CMessage {
  GetRequest{ k: CKey},
  SetRequest{ k: CKey, v: Option::<Vec<u8>>},
  Reply{ k: CKey, v: Option::<Vec::<u8>> },
  Redirect{ k: CKey, id: EndPoint },
  Shard{ kr: KeyRange::<CKey>, recipient: EndPoint },
  Delegate{ range: KeyRange::<CKey>, h: CKeyHashMap},
}

pub struct CPacket {
  pub dst: EndPoint,
  pub src: EndPoint,
  pub msg: CSingleMessage,
}

/*delegation_map_v.rs*/

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
    // Our efficient implementation based on ranges
    lows: StrictlyOrderedMap<K>,
    // Our spec version
    m: Ghost<Map<K, AbstractEndPoint>>,

}

/*endpoint_hashmap_t*/
#[verifier(external_body)]
#[verifier::accept_recursive_types(V)]
pub struct HashMap<V> {
  m: collections::HashMap<EndPoint, V>,
}

/*hashmap_t*/

pub struct CKeyHashMap {
  m: collections::HashMap<CKey, Vec<u8>>,
}

impl CKeyHashMap {

    pub uninterp spec fn view(self) -> Map<AbstractKey, Seq<u8>>;

}

/*host_impl_v*/

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

    proof fn effect_of_hashmap_bulk_update(
        pre: CKeyHashMap,
        post: CKeyHashMap,
        kr: &KeyRange::<CKey>,
        other: CKeyHashMap
    )
        requires
            forall |k| pre@.dom().contains(k) ==> #[trigger] valid_value(pre@[k]),
            valid_hashtable(other@),
            post@ == Map::<AbstractKey, Seq<u8>>::new(
                |k: AbstractKey| (pre@.dom().contains(k) || other@.dom().contains(k))
                                 && (kr.contains(k) ==> other@.dom().contains(k)),
                |k: AbstractKey| if other@.dom().contains(k) { other@[k] } else { pre@[k] }
            ),
       ensures
           post@ == bulk_update_hashtable(pre@, *kr, other@),
           forall |k| post@.dom().contains(k) ==> #[trigger] valid_value(post@[k])
    {
        assert_maps_equal!(post@, bulk_update_hashtable(pre@, *kr, other@));
    }

}

/*host_protocol_t*/

pub open spec fn max_hashtable_size() -> int
{
    62
}

pub open spec fn valid_hashtable(h: Hashtable) -> bool
{
    &&& h.dom().len() < max_hashtable_size()
    &&& (forall |k| h.dom().contains(k) ==> valid_key(k) && #[trigger] valid_value(h[k]))
}

pub open spec(checked) fn bulk_update_domain(h: Hashtable, kr: KeyRange<AbstractKey>, u: Hashtable) -> Set<AbstractKey>
{
    Set::<AbstractKey>::new(|k| (h.dom().contains(k) || u.dom().contains(k))
                                && (kr.contains(k) ==> u.dom().contains(k)))
}

pub open spec /*(checked) because lambdas*/ fn bulk_update_hashtable(h: Hashtable, kr: KeyRange<AbstractKey>, u: Hashtable) -> Hashtable
{
    Map::<AbstractKey, AbstractValue>::new(
        |k: AbstractKey| bulk_update_domain(h, kr, u).contains(k),
        |k: AbstractKey| if u.dom().contains(k) { u[k] } else { h[k] }
    )
}


/*io_t*/
pub struct EndPoint {
    pub id: Vec<u8>,
}

/*keys_t*/

pub trait KeyTrait : Sized {

    spec fn cmp_spec(self, other: Self) -> Ordering;

}

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

    pub open spec fn new_spec(k: K) -> Self {
        KeyIterator { k: Some(k) }
    }

    pub open spec fn lt_spec(self, other: Self) -> bool {
        (!self.k.is_None() && other.k.is_None())
      || (!self.k.is_None() && !other.k.is_None() && self.k.get_Some_0().cmp_spec(other.k.get_Some_0()).lt())
    }

}


pub struct KeyRange<K: KeyTrait + VerusClone> {
    pub lo: KeyIterator<K>,
    pub hi: KeyIterator<K>,
}

impl<K: KeyTrait + VerusClone> KeyRange<K> {

    pub open spec fn contains(self, k: K) -> bool
    {
        KeyIterator::<K>::between(self.lo, KeyIterator::<K>::new_spec(k), self.hi)
    }

}


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

/*marshal_v*/

pub enum CSingleMessage {
    Message{ seqno: u64, dst: EndPoint, m:CMessage},
    Ack {ack_seqno: u64},
    InvalidMessage,
}
/*
    enum $newenum $(< $($poly : Marshalable),+ >)? {
      $($variant $( { $($member : $memberty),* } )?),+
    }
*/

/*single_Delivery_state_v*/
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

//trait impl
impl VerusClone for SHTKey{}

//missed
pub type AbstractKey = SHTKey;
pub type CKey = SHTKey;
pub type Hashtable = Map<AbstractKey, AbstractValue>;
pub type AbstractValue = Seq<u8>;
type ID = EndPoint;

//why?
pub struct AbstractEndPoint {
    pub id: Seq<u8>,
}

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


}
