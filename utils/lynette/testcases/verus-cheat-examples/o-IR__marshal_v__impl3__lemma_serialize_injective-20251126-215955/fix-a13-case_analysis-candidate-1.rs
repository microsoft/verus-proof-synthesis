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
                    assert(true);
                } else {
                    let o = other.get_Some_0();
                    // substitute serializations for None vs Some and use equality to get first-byte equality
                    assert(self.ghost_serialize() == seq![0u8]);
                    assert(other.ghost_serialize() == seq![1u8] + o.ghost_serialize());
                    assert(self.ghost_serialize()[0] == other.ghost_serialize()[0]);
                    // substitute concrete first bytes (0 vs 1) giving contradiction
                    assert(seq![0u8][0] != (seq![1u8] + o.ghost_serialize())[0]);
                    assert(false);
                }
            } else {
                let s = self.get_Some_0();
                if other.is_None() {
                    // substitute serializations for Some vs None and use equality to get first-byte equality
                    assert(self.ghost_serialize() == seq![1u8] + s.ghost_serialize());
                    assert(other.ghost_serialize() == seq![0u8]);
                    assert(self.ghost_serialize()[0] == other.ghost_serialize()[0]);
                    // substitute concrete first bytes (1 vs 0) giving contradiction
                    assert((seq![1u8] + s.ghost_serialize())[0] != seq![0u8][0]);
                    assert(false);
                } else {
                    let o = other.get_Some_0();
                    // substitute serializations for Some vs Some and strip the leading tag
                    assert(self.ghost_serialize() == seq![1u8] + s.ghost_serialize());
                    assert(other.ghost_serialize() == seq![1u8] + o.ghost_serialize());
                    assert(self.ghost_serialize().subrange(1, self.ghost_serialize().len() as int)
                        == other.ghost_serialize().subrange(1, other.ghost_serialize().len() as int));
                    assert((seq![1u8] + s.ghost_serialize()).subrange(1, (seq![1u8] + s.ghost_serialize()).len() as int)
                        == s.ghost_serialize());
                    assert((seq![1u8] + o.ghost_serialize()).subrange(1, (seq![1u8] + o.ghost_serialize()).len() as int)
                        == o.ghost_serialize());
                    assert(s.ghost_serialize() == o.ghost_serialize());
                    // inner values are marshalable
                    assert(s.is_marshalable());
                    assert(o.is_marshalable());
                    s.lemma_serialize_injective(&o);
                    // substitute value of view_equal for (Some, Some)
                    assert(s.view_equal(&o));
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
// Reasoning: Pipeline Analysis: The assertion self.view_equal(other) is attempted without any assumptions; injectivity for Option requires the trait’s preconditions (marshalability and equality of ghost_serialize). Without those, the goal is not derivable.
// Secondary Actions: ['seqsetmap', 'uselemma']
// 
// Parameters:
//   assertion_content: self.view_equal(other)
//   guidance: Refactor the lemma to match the trait’s requires/ensures so you can assume self.is_marshalable(), other.is_marshalable(), and self.ghost_serialize() == other.ghost_serialize(). Then case-analyze (self, other): None/Some and Some/None contradict due to first byte 0 vs 1; Some/Some lets you strip the leading tag to conclude s.ghost_serialize() == o.ghost_serialize(). Use sequence APIs (len, indexing, subrange, concatenation) to justify tail equality, and finally call T::lemma_serialize_injective(s, o) to conclude s.view_equal(o).
// 
// ACTION PHASE:
// Action Type: case_analysis
// Success: True
// Accepted: False
// Explanation: Generated 1 case_analysis candidates (guidance: Refactor the lemma to match the trait’s requires/ensures so you can assume self.is_marshalable(), ot...)
// Action Parameters:
//   guidance: Refactor the lemma to match the trait’s requires/ensures so you can assume self.is_marshalable(), other.is_marshalable(), and self.ghost_serialize() == other.ghost_serialize(). Then case-analyze (self, other): None/Some and Some/None contradict due to first byte 0 vs 1; Some/Some lets you strip the leading tag to conclude s.ghost_serialize() == o.ghost_serialize(). Use sequence APIs (len, indexing, subrange, concatenation) to justify tail equality, and finally call T::lemma_serialize_injective(s, o) to conclude s.view_equal(o).
// 
// CANDIDATES:
// Total Candidates: 1
// Has Multiple Candidates: False
// Agent Class: AssertionErrorAgent
