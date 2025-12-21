use vstd::prelude::*;
fn main() {}
verus! {

#[derive(Eq, PartialEq, Hash)]
pub struct SHTKey {
    pub ukey: u64,
}

pub type AbstractKey = SHTKey;

pub type CKey = SHTKey;

pub struct CKeyKV {
    pub k: CKey,
    pub v: Vec<u8>,
}

impl CKeyKV {
    pub open spec fn view(self) -> (AbstractKey, Seq<u8>) {
        (self.k, self.v@)
    }
}

pub open spec fn ckeykvlt(a: CKeyKV, b: CKeyKV) -> bool {
    a.k.ukey < b.k.ukey
}

pub open spec fn spec_sorted_keys(v: Vec<CKeyKV>) -> bool {
    forall|i: int, j: int|
        0 <= i && i + 1 < v.len() && j == i + 1 ==> #[trigger] ckeykvlt(v@[i], v@[j])
}

impl SHTKey {
    pub fn clone(&self) -> (out: SHTKey)
        ensures
            out == self,
    {
        SHTKey { ukey: self.ukey }
    }
}

pub exec fn sorted_keys(v: &Vec<CKeyKV>) -> (res: bool)
    ensures
        res == spec_sorted_keys(*v),
{
    if v.len() <= 1 {
        true
    } else {
        let mut idx = 1;
        while idx < v.len() {
            if v[idx - 1].k.ukey >= v[idx].k.ukey {
                return false;
            } else {
                idx = idx + 1;
            }
        }
        true
    }
}

} // verus!
