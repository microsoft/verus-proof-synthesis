use vstd::prelude::*;

fn main() {}

verus! {
#[derive(Eq,PartialEq,Hash)]
pub struct SHTKey {
    pub // workaround
        ukey: u64,
}

impl SHTKey {
    pub fn clone(&self) -> (out: SHTKey)
    ensures out == self
    {
        SHTKey{ ukey: self.ukey }
    }
}

pub type AbstractKey = SHTKey;
pub type CKey = SHTKey;


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

pub exec fn sorted_keys(v: &Vec<CKeyKV>) -> (res: bool)
    ensures res == spec_sorted_keys(*v),
{
    if v.len() <= 1 {
        true
    } else {
        let mut idx = 1;
        while idx < v.len()
            invariant
                (0 < idx <= v.len()),
                (forall |i: int, j: int| 0 <= i && i + 1 < idx && j == i+1 ==> #[trigger] ckeykvlt(v@[i], v@[j])),
                decreases
                    v.len() - idx
                    {
                        if v[idx - 1].k.ukey >= v[idx].k.ukey {
                            assert(!ckeykvlt(v@[idx as int-1], v@[idx as int]));
                            return false;
                        } else {
                            idx = idx + 1;
                        }
                    }
        assert forall |i: int| 0 <= i && i + 1 < v.len() implies #[trigger] v@[i].k.ukey < v@[i + 1].k.ukey by {
            assert(ckeykvlt(v@[i], v@[i + 1])); // OBSERVE
        }
        true
    }
}

}
