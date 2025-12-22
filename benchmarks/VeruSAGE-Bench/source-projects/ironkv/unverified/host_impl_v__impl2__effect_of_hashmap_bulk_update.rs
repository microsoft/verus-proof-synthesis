extern crate verus_builtin_macros as builtin_macros;
use std::collections;
use vstd::prelude::*;
fn main() {}
verus! {

pub trait VerusClone {
}

pub enum Ordering {
    Less,
    Equal,
    Greater,
}

impl Ordering {
    pub open spec fn lt(self) -> bool {
        matches!(self, Ordering::Less)
    }
}

pub trait KeyTrait: Sized {
    spec fn cmp_spec(self, other: Self) -> Ordering;
}

pub struct KeyIterator<K: KeyTrait + VerusClone> {
    pub k: Option<K>,
}

impl<K: KeyTrait + VerusClone> KeyIterator<K> {
    pub open spec fn between(lhs: Self, ki: Self, rhs: Self) -> bool {
        !ki.lt_spec(lhs) && ki.lt_spec(rhs)
    }
}

impl<K: KeyTrait + VerusClone> KeyIterator<K> {
    pub open spec fn new_spec(k: K) -> Self {
        KeyIterator { k: Some(k) }
    }

    pub open spec fn lt_spec(self, other: Self) -> bool {
        (!self.k.is_None() && other.k.is_None()) || (!self.k.is_None() && !other.k.is_None()
            && self.k.get_Some_0().cmp_spec(other.k.get_Some_0()).lt())
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
}

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

impl VerusClone for SHTKey {}

pub type AbstractKey = SHTKey;

pub type CKey = SHTKey;

pub type AbstractValue = Seq<u8>;

pub type Hashtable = Map<AbstractKey, AbstractValue>;

pub struct EndPoint {
    pub id: Vec<u8>,
}

type ID = EndPoint;

pub struct AbstractEndPoint {
    pub id: Seq<u8>,
}

pub enum AppRequest {
    AppGetRequest { seqno: nat, key: AbstractKey },
    AppSetRequest { seqno: nat, key: AbstractKey, ov: Option<AbstractValue> },
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

#[verifier(external_body)]
#[verifier::accept_recursive_types(V)]
pub struct HashMap<V> {
    m: collections::HashMap<EndPoint, V>,
}

pub struct CKeyHashMap {
    m: collections::HashMap<CKey, Vec<u8>>,
}

impl CKeyHashMap {
    pub uninterp spec fn view(self) -> Map<AbstractKey, Seq<u8>>;
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

#[allow(inconsistent_fields)]
pub enum CMessage {
    GetRequest { k: CKey },
    SetRequest { k: CKey, v: Option::<Vec<u8>> },
    Reply { k: CKey, v: Option::<Vec::<u8>> },
    Redirect { k: CKey, id: EndPoint },
    Shard { kr: KeyRange::<CKey>, recipient: EndPoint },
    Delegate { range: KeyRange::<CKey>, h: CKeyHashMap },
}

pub enum CSingleMessage {
    Message { seqno: u64, dst: EndPoint, m: CMessage },
    Ack { ack_seqno: u64 },
    InvalidMessage,
}

pub struct CPacket {
    pub dst: EndPoint,
    pub src: EndPoint,
    pub msg: CSingleMessage,
}

pub struct CAckState {
    pub num_packets_acked: u64,
    pub un_acked: Vec<CSingleMessage>,
}

pub struct CTombstoneTable {
    pub epmap: HashMap<u64>,
}

pub struct CSendState {
    pub epmap: HashMap<CAckState>,
}

pub struct CSingleDelivery {
    pub receive_state: CTombstoneTable,
    pub send_state: CSendState,
}


#[verifier::reject_recursive_types(K)]
struct StrictlyOrderedMap<K: KeyTrait + VerusClone> {
    keys: StrictlyOrderedVec<K>,
    vals: Vec<ID>,
    m: Ghost<Map<K, ID>>,
}

struct StrictlyOrderedVec<K: KeyTrait> {
    v: Vec<K>,
}

#[verifier::reject_recursive_types(K)]
pub struct DelegationMap<K: KeyTrait + VerusClone> {
    lows: StrictlyOrderedMap<K>,
    m: Ghost<Map<K, AbstractEndPoint>>,
}

pub struct Parameters {
    pub max_seqno: u64,
    pub max_delegations: u64,
}

pub struct Constants {
    pub root_identity: EndPoint,
    pub host_ids: Vec<EndPoint>,
    pub params: Parameters,
    pub me: EndPoint,
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


impl HostState {
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
    }
}

} // verus!
