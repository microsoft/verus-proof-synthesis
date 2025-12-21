use vstd::bytes::*;
use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::external_body]
pub proof fn lemma_seq_fold_left_sum_right<A>(s: Seq<A>, low: int, f: spec_fn(A) -> int)
    requires
        s.len() > 0,
    ensures
        s.subrange(0, s.len() - 1).fold_left(low, |b: int, a: A| b + f(a)) + f(s[s.len() - 1])
            == s.fold_left(low, |b: int, a: A| b + f(a)),
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn lemma_seq_fold_left_append_len_int_le<A, B>(
    s: Seq<A>,
    i: int,
    low: int,
    f: spec_fn(A) -> Seq<B>,
)
    requires
        0 <= i <= s.len() as int,
        0 <= low,
    ensures
        s.fold_left(low, |acc: int, x: A| acc + f(x).len()) >= 0,
        s.subrange(0, i).fold_left(low, |acc: int, x: A| acc + f(x).len()) <= s.fold_left(
            low,
            |acc: int, x: A| acc + f(x).len(),
        ),
    decreases (2 * s.len() - i),
{
    unimplemented!()
}

pub trait Marshalable: Sized {
    spec fn is_marshalable(&self) -> bool;

    #[verifier::external_body]
    exec fn _is_marshalable(&self) -> (res: bool)
        ensures
            res == self.is_marshalable(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    spec fn ghost_serialize(&self) -> Seq<u8>
        recommends
            self.is_marshalable(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    exec fn serialized_size(&self) -> (res: usize)
        requires
            self.is_marshalable(),
        ensures
            res as int == self.ghost_serialize().len(),
    {
        unimplemented!()
    }
}

impl Marshalable for u64 {
    open spec fn is_marshalable(&self) -> bool {
        true
    }

    #[verifier::external_body]
    exec fn _is_marshalable(&self) -> (res: bool) {
        unimplemented!()
    }

    open spec fn ghost_serialize(&self) -> Seq<u8> {
        spec_u64_to_le_bytes(*self)
    }

    #[verifier::external_body]
    exec fn serialized_size(&self) -> (res: usize) {
        unimplemented!()
    }
}

impl Marshalable for usize {
    open spec fn is_marshalable(&self) -> bool {
        &&& *self as int <= u64::MAX
    }

    #[verifier::external_body]
    exec fn _is_marshalable(&self) -> (res: bool) {
        unimplemented!()
    }

    open spec fn ghost_serialize(&self) -> Seq<u8> {
        (*self as u64).ghost_serialize()
    }

    #[verifier::external_body]
    exec fn serialized_size(&self) -> (res: usize) {
        unimplemented!()
    }
}

impl Marshalable for Vec<u8> {
    open spec fn is_marshalable(&self) -> bool {
        self@.len() <= usize::MAX && (self@.len() as usize).ghost_serialize().len()
            + self@.len() as int <= usize::MAX
    }

    #[verifier::external_body]
    exec fn _is_marshalable(&self) -> (res: bool) {
        unimplemented!()
    }

    open spec fn ghost_serialize(&self) -> Seq<u8> {
        (self@.len() as usize).ghost_serialize() + self@
    }

    #[verifier::external_body]
    exec fn serialized_size(&self) -> (res: usize) {
        unimplemented!()
    }
}

impl<T: Marshalable> Marshalable for Vec<T> {
    open spec fn is_marshalable(&self) -> bool {
        &&& self@.len() <= usize::MAX
        &&& (forall|x: T| self@.contains(x) ==> #[trigger] x.is_marshalable())
        &&& (self@.len() as usize).ghost_serialize().len() + self@.fold_left(
            0,
            |acc: int, x: T| acc + x.ghost_serialize().len(),
        ) <= usize::MAX
    }

    open spec fn ghost_serialize(&self) -> Seq<u8> {
        (self@.len() as usize).ghost_serialize() + self@.fold_left(
            Seq::<u8>::empty(),
            |acc: Seq<u8>, x: T| acc + x.ghost_serialize(),
        )
    }

    #[verifier::external_body]
    exec fn serialized_size(&self) -> (res: usize) {
        unimplemented!()
    }

    exec fn _is_marshalable(&self) -> bool {
        let mut res = true;
        let mut i = 0;
        let mut total_len = self.len().serialized_size();
        while res && i < self.len() {
            res =
            res && self[i]._is_marshalable() && (usize::MAX - total_len >= self[i].serialized_size());
        }
        res
    }
}

} // verus!
