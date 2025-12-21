use std::collections;
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

pub struct CPacket {
    pub dst: EndPoint,
    pub src: EndPoint,
    pub msg: CSingleMessage,
}

#[verifier::reject_recursive_types(K)]
pub struct DelegationMap<K: KeyTrait + VerusClone> {
    lows: StrictlyOrderedMap<K>,
    m: Ghost<Map<K, AbstractEndPoint>>,
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

    #[verifier::external_body]
    pub fn static_params() -> (out: Parameters)
        ensures
            out@ == AbstractParameters::static_params(),
    {
        unimplemented!()
    }
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

pub struct AbstractEndPoint {
    pub id: Seq<u8>,
}

impl AbstractEndPoint {
    pub open spec fn valid_physical_address(self) -> bool {
        self.id.len() < 0x100000
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

#[verifier::accept_recursive_types(V)]
#[verifier(external_body)]
pub struct HashMap<V> {
    m: collections::HashMap<EndPoint, V>,
}

#[verifier(external_body)]
pub struct CKeyHashMap {
    m: collections::HashMap<CKey, Vec<u8>>,
}

pub struct AbstractConstants {
    pub root_identity: AbstractEndPoint,
    pub host_ids: Seq<AbstractEndPoint>,
    pub params: AbstractParameters,
    pub me: AbstractEndPoint,
}

pub open spec fn parse_arg_as_end_point(arg: AbstractArg) -> AbstractEndPoint {
    AbstractEndPoint { id: arg }
}

pub open spec fn unchecked_parse_args(args: AbstractArgs) -> Seq<AbstractEndPoint> {
    args.map(|idx, arg: AbstractArg| parse_arg_as_end_point(arg))
}

pub open spec(checked) fn parse_args(args: AbstractArgs) -> Option<Seq<AbstractEndPoint>> {
    let end_points = unchecked_parse_args(args);
    if forall|i| #![auto] 0 <= i < end_points.len() ==> end_points[i].valid_physical_address() {
        Some(end_points)
    } else {
        None
    }
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
}

pub open spec fn abstractify_end_points(end_points: Vec<EndPoint>) -> Seq<AbstractEndPoint> {
    end_points@.map(|i, end_point: EndPoint| end_point@)
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

#[verifier::opaque]
pub open spec fn seq_is_unique<T>(s: Seq<T>) -> bool {
    forall|i: int, j: int|
        #![trigger s[i], s[j]]
        0 <= i && i < s.len() && 0 <= j && j < s.len() && s[i] == s[j] ==> i == j
}

#[verifier::external_body]
pub fn test_unique(endpoints: &Vec<EndPoint>) -> (unique: bool)
    ensures
        unique == seq_is_unique(abstractify_end_points(*endpoints)),
{
    unimplemented!()
}

pub open spec fn abstractify_args(args: Args) -> AbstractArgs {
    args@.map(|i, arg: Arg| arg@)
}

pub trait KeyTrait {

}

pub trait VerusClone {

}

impl VerusClone for SHTKey {

}

impl KeyTrait for SHTKey {

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

pub enum CSingleMessage {
    Message { seqno: u64, dst: EndPoint, m: CMessage },
    Ack { ack_seqno: u64 },
    InvalidMessage,
}

impl HostState {
    #[verifier::external_body]
    fn parse_end_points(args: &Args) -> (out: Option<Vec<EndPoint>>)
        ensures
            match out {
                None => parse_args(abstractify_args(*args)) is None,
                Some(vec) => {
                    &&& parse_args(abstractify_args(*args)) is Some
                    &&& abstractify_end_points(vec) == parse_args(abstractify_args(*args)).unwrap()
                },
            },
    {
        unimplemented!()
    }

    fn parse_command_line_configuration(args: &Args, me: EndPoint) -> (rc: Option<Constants>)
        ensures
            ({
                let abstract_end_points = parse_args(abstractify_args(*args));
                match rc {
                    None => {
                        ||| abstract_end_points.is_None()
                        ||| abstract_end_points.unwrap().len() == 0
                        ||| !seq_is_unique(abstract_end_points.unwrap())
                    },
                    Some(c) => {
                        &&& abstract_end_points.is_some()
                        &&& abstract_end_points.unwrap().len() > 0
                        &&& seq_is_unique(abstract_end_points.unwrap())
                        &&& c@ == AbstractConstants {
                            root_identity: abstract_end_points.unwrap()[0],
                            host_ids: abstract_end_points.unwrap(),
                            params: AbstractParameters::static_params(),
                            me: me@,
                        }
                    },
                }
            }),
    {
        let end_points = Self::parse_end_points(args);
        if matches!(end_points,
    None) {
            return None;
        }
        let ghost abstract_end_points: Option<Seq<AbstractEndPoint>> = arbitrary(); // TODO - replace with correct value
        let end_points: Vec<EndPoint> = end_points.unwrap();
        if end_points.len() == 0 {
            return None;
        }
        let unique = test_unique(&end_points);
        if !unique {
            return None;
        }
        let constants = Constants {
            root_identity: end_points[0].clone_up_to_view(),
            host_ids: end_points,
            params: Parameters::static_params(),
            me: me,
        };
        let ret = Some(constants);
        ret
    }
}

} // verus!
