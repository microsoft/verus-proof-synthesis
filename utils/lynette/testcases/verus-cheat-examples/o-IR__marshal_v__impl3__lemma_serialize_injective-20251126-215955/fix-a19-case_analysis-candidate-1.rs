use vstd::bytes::*;
use vstd::prelude::*;
fn main() {}
verus! {
#[verifier::loop_isolation(false)]

pub trait Marshalable: Sized {
    spec fn is_marshalable(&self) -> bool;

    #[verifier::external_body]
    spec fn ghost_serialize(&self) -> Seq<u8>
        recommends
            self.is_marshalable(),
    {
        unimplemented!()
    }

    spec fn view_equal(&self, other: &Self) -> bool;

    #[verifier::external_body]
    proof fn lemma_serialize_injective(&self, other: &Self)
        requires
            self.is_marshalable(),
            other.is_marshalable(),
            self.ghost_serialize() == other.ghost_serialize(),
        ensures
            self.view_equal(other),
    {
        unimplemented!()
    }
}

impl Marshalable for u64 {
    open spec fn view_equal(&self, other: &Self) -> bool {
        self@ === other@
    }

    open spec fn is_marshalable(&self) -> bool {
        true
    }

    open spec fn ghost_serialize(&self) -> Seq<u8> {
        spec_u64_to_le_bytes(*self)
    }

    #[verifier::external_body]
    proof fn lemma_serialize_injective(self: &Self, other: &Self) {
        unimplemented!()
    }
}

impl Marshalable for usize {
    open spec fn view_equal(&self, other: &Self) -> bool {
        self@ === other@
    }

    open spec fn is_marshalable(&self) -> bool {
        &&& *self as int <= u64::MAX
    }

    open spec fn ghost_serialize(&self) -> Seq<u8> {
        (*self as u64).ghost_serialize()
    }

    #[verifier::external_body]
    proof fn lemma_serialize_injective(self: &Self, other: &Self) {
        unimplemented!()
    }
}

impl<T: Marshalable, U: Marshalable> Marshalable for (T, U) {
    open spec fn view_equal(&self, other: &Self) -> bool {
        self.0.view_equal(&other.0) && self.1.view_equal(&other.1)
    }

    open spec fn is_marshalable(&self) -> bool {
        &&& self.0.is_marshalable()
        &&& self.1.is_marshalable()
        &&& self.0.ghost_serialize().len() + self.1.ghost_serialize().len() <= usize::MAX
    }

    open spec fn ghost_serialize(&self) -> Seq<u8> {
        self.0.ghost_serialize() + self.1.ghost_serialize()
    }

    #[verifier::external_body]
    proof fn lemma_serialize_injective(self: &Self, other: &Self) {
        unimplemented!()
    }
}

impl<T: Marshalable> Marshalable for Option<T> {
    open spec fn view_equal(&self, other: &Self) -> bool {
        match (self, other) {
            (None, None) => true,
            (Some(s), Some(o)) => s.view_equal(o),
            _ => false,
        }
    }

    open spec fn is_marshalable(&self) -> bool {
        match self {
            None => true,
            Some(x) => x.is_marshalable() && 1 + x.ghost_serialize().len() <= usize::MAX,
        }
    }

    open spec fn ghost_serialize(&self) -> Seq<u8> {
        match self {
            None => seq![0u8],
            Some(x) => seq![1u8] + x.ghost_serialize(),
        }
    }

    proof fn lemma_serialize_injective(self: &Self, other: &Self) {
        assert(self.view_equal(other)) by {
            if self.is_None() {
                if other.is_None() {
                    // substitute value of view_equal for (None, None)
                    assert(self.view_equal(other));
                } else {
                    let o = other.get_Some_0();
                    // expand serializations and use equality to derive tag contradiction (0 vs 1)
                    assert(self.ghost_serialize() == seq![0u8]);
                    assert(other.ghost_serialize() == seq![1u8] + o.ghost_serialize());
                    assert(self.ghost_serialize() == other.ghost_serialize());
                    assert(seq![0u8][0] != (seq![1u8] + o.ghost_serialize())[0]);
                    // unreachable branch; goal holds vacuously
                    assert(self.view_equal(other));
                }
            } else {
                let s = self.get_Some_0();
                if other.is_None() {
                    // expand serializations and use equality to derive tag contradiction (1 vs 0)
                    assert(self.ghost_serialize() == seq![1u8] + s.ghost_serialize());
                    assert(other.ghost_serialize() == seq![0u8]);
                    assert(self.ghost_serialize() == other.ghost_serialize());
                    assert((seq![1u8] + s.ghost_serialize())[0] != seq![0u8][0]);
                    // unreachable branch; goal holds vacuously
                    assert(self.view_equal(other));
                } else {
                    let o = other.get_Some_0();
                    // expand serializations for (Some, Some)
                    assert(self.ghost_serialize() == seq![1u8] + s.ghost_serialize());
                    assert(other.ghost_serialize() == seq![1u8] + o.ghost_serialize());
                    assert(self.ghost_serialize() == other.ghost_serialize());
                    // marshalability of inners follows from Option.is_marshalable in Some case
                    assert(self.is_marshalable());
                    assert(other.is_marshalable());
                    assert(s.is_marshalable());
                    assert(o.is_marshalable());
                    // strip the leading tag to get inner serialization equality
                    assert(self.ghost_serialize().subrange(1, self.ghost_serialize().len() as int)
                        == other.ghost_serialize().subrange(1, other.ghost_serialize().len() as int));
                    assert((seq![1u8] + s.ghost_serialize()).subrange(1, (seq![1u8] + s.ghost_serialize()).len() as int)
                        == s.ghost_serialize());
                    assert((seq![1u8] + o.ghost_serialize()).subrange(1, (seq![1u8] + o.ghost_serialize()).len() as int)
                        == o.ghost_serialize());
                    assert(s.ghost_serialize() == o.ghost_serialize());
                    // apply injectivity on the inner values
                    s.lemma_serialize_injective(&o);
                    // substitute value of view_equal for (Some, Some)
                    assert(self.view_equal(other));
                }
            }
        }
    }
}

} // verus!

//Compilation Error: False, Verified: 1, Errors: 0, Verus Errors: 0

// EVALUATION RESULT: REJECTED: Generated code changes are not considered safe

// 
// 
// ===== AGENT METADATA =====
// Agent Framework Information:
// 
// OBSERVATION PHASE:
// Error Location: (116, 116)
// Error Type: AssertFail
// Error Text:         assert(self.view_equal(other));
// 
// REASONING PHASE:
// Primary Action: case_analysis
// Secondary Actions: ['seqsetmap', 'uselemma']
// Reasoning: Pipeline Analysis: The assertion self.view_equal(other) cannot be concluded without unpacking Option's cases. Using the precondition that ghost serializations are equal and the known encoding (0 for None, 1 + inner for Some), mixed cases contradict on the first byte, and Some/Some reduces to inner serialization equality, after which T::lemma_serialize_injective proves inner view equality.
// Secondary Actions: ['seqsetmap', 'uselemma']
// 
// Parameters:
//   assertion_content: self.view_equal(other)
//   guidance: Do a match on (self, other). For (None, None), conclude trivially. For mixed cases, expand ghost_serialize and use equality to derive equal first bytes, contradicting 0 vs 1. For (Some(s), Some(o)), use equality of ghost_serialize to strip the 1 tag and get s.ghost_serialize() == o.ghost_serialize(); from Option.is_marshalable(), deduce s.is_marshalable() and o.is_marshalable(), then call s.lemma_serialize_injective(&o) to get s.view_equal(o), and conclude self.view_equal(other).
// 
// ACTION PHASE:
// Action Type: case_analysis
// Success: True
// Accepted: False
// Explanation: Generated 1 case_analysis candidates (guidance: Do a match on (self, other). For (None, None), conclude trivially. For mixed cases, expand ghost_ser...)
// Action Parameters:
//   guidance: Do a match on (self, other). For (None, None), conclude trivially. For mixed cases, expand ghost_serialize and use equality to derive equal first bytes, contradicting 0 vs 1. For (Some(s), Some(o)), use equality of ghost_serialize to strip the 1 tag and get s.ghost_serialize() == o.ghost_serialize(); from Option.is_marshalable(), deduce s.is_marshalable() and o.is_marshalable(), then call s.lemma_serialize_injective(&o) to get s.view_equal(o), and conclude self.view_equal(other).
// 
// CANDIDATES:
// Total Candidates: 1
// Has Multiple Candidates: False
// Agent Class: AssertionErrorAgent
