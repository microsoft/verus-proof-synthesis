use vstd::prelude::*;
fn main() {}
verus! {

pub type Hashtable = Map<AbstractKey, AbstractValue>;

#[derive(Eq, PartialEq,
    Hash)]
pub struct SHTKey {
    pub ukey: u64,
}

pub type AbstractKey = SHTKey;

pub type AbstractValue = Seq<u8>;

pub type CKey = SHTKey;

pub trait KeyTrait: Sized {

}

pub trait VerusClone: Sized {
    fn clone(&self) -> (o: Self)
        ensures
            o == self,
    ;
}

impl<K: VerusClone + KeyTrait> VerusClone for KeyIterator<K> {
    fn clone(&self) -> Self {
        KeyIterator {
            k: match &self.k {
                Some(v) => Some(v.clone()),
                None => None,
            },
        }
    }
}

impl<K: VerusClone + KeyTrait> VerusClone for KeyRange<K> {
    fn clone(&self) -> Self {
        KeyRange { lo: self.lo.clone(), hi: self.hi.clone() }
    }
}

impl KeyTrait for SHTKey {

}

impl VerusClone for SHTKey {
    fn clone(&self) -> (o: Self) {
        SHTKey { ukey: self.ukey }
    }
}

#[derive(PartialEq, Eq, Hash)]
pub struct EndPoint {
    pub id: Vec<u8>,
}

impl EndPoint {
    pub open spec fn view(self) -> AbstractEndPoint {
        AbstractEndPoint { id: self.id@ }
    }
}

pub struct AbstractEndPoint {
    pub id: Seq<u8>,
}

pub struct KeyRange<K: KeyTrait + VerusClone> {
    pub lo: KeyIterator<K>,
    pub hi: KeyIterator<K>,
}

pub struct KeyIterator<K: KeyTrait + VerusClone> {
    pub k: Option<K>,
}

pub type PMsg = SingleMessage<Message>;

#[doc =
    " A Packet is an abstract version of a `CPacket`."]
#[doc = ""]
#[doc =
    " It's isomorphic to an `LSHTPacket = LPacket<AbstractEndPoint,"]
#[doc =
    " SingleMessage<Message>>`."]
pub struct Packet {
    pub dst: AbstractEndPoint,
    pub src: AbstractEndPoint,
    pub msg: PMsg,
}

pub type SendState<MT> = Map<AbstractEndPoint, AckState<MT>>;

pub type TombstoneTable = Map<AbstractEndPoint, nat>;

pub type AckList<MT> = Seq<SingleMessage<MT>>;

pub struct AckState<MT> {
    pub num_packets_acked: nat,
    pub un_acked: AckList<MT>,
}

impl AckState<Message> {
    pub open spec fn new() -> Self {
        AckState { num_packets_acked: 0, un_acked: seq![] }
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
pub struct SingleDelivery<MT> {
    pub receive_state: TombstoneTable,
    pub send_state: SendState<MT>,
}

pub open spec fn flatten_sets<A>(sets: Set<Set<A>>) -> Set<A> {
    Set::new(|a: A| (exists|s: Set<A>| sets.contains(s) && s.contains(a)))
}

impl SingleDelivery<Message> {
    pub open spec(checked) fn un_acked_messages_for_dest_up_to(
        self,
        src: AbstractEndPoint,
        dst: AbstractEndPoint,
        count: nat,
    ) -> Set<Packet>
        recommends
            self.send_state.contains_key(dst),
            count <= self.send_state[dst].un_acked.len(),
    {
        Set::new(
            |p: Packet|
                {
                    &&& p.src == src
                    &&& exists|i: int|
                        {
                            &&& 0 <= i < count
                            &&& self.send_state[dst].un_acked[i] is Message
                            &&& p.msg == self.send_state[dst].un_acked[i]
                            &&& p.dst == p.msg.arrow_Message_dst()
                        }
                },
        )
    }

    pub open spec(checked) fn un_acked_messages_for_dest(
        self,
        src: AbstractEndPoint,
        dst: AbstractEndPoint,
    ) -> Set<Packet>
        recommends
            self.send_state.contains_key(dst),
    {
        self.un_acked_messages_for_dest_up_to(src, dst, self.send_state[dst].un_acked.len())
    }

    pub open spec fn un_acked_messages_for_dests(
        self,
        src: AbstractEndPoint,
        dsts: Set<AbstractEndPoint>,
    ) -> Set<Packet>
        recommends
            dsts.subset_of(self.send_state.dom()),
    {
        flatten_sets(dsts.map(|dst: AbstractEndPoint| self.un_acked_messages_for_dest(src, dst)))
    }

    pub proof fn lemma_un_acked_messages_for_dests_empty(
        &self,
        src: AbstractEndPoint,
        dests: Set<AbstractEndPoint>,
    )
        requires
            dests == Set::<AbstractEndPoint>::empty(),
        ensures
            self.un_acked_messages_for_dests(src, dests) == Set::<Packet>::empty(),
    {
    }
}

pub enum SingleMessage<MT> {
    Message { seqno: nat, dst: AbstractEndPoint, m: MT },
    Ack { ack_seqno: nat },
    InvalidMessage {  },
}

impl SHTKey {
    pub fn clone(&self) -> (out: SHTKey)
        ensures
            out == self,
    {
        SHTKey { ukey: self.ukey }
    }
}

} // verus!
