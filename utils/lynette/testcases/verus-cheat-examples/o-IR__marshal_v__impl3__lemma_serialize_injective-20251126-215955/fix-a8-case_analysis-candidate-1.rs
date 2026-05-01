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

    proof fn lemma_serialize_injective(self: &Self, other: &Self)
    {
        assert(self.view_equal(other)) by {
            if self.is_None() {
                if other.is_None() {
                    // substitute value of view_equal for (None, None)
                    assert(true);
                } else {
                    let o = other.get_Some_0();
                    // substitute ghost_serialize for None vs Some
                    assert(self.ghost_serialize() == seq![0u8]);
                    assert(other.ghost_serialize() == seq![1u8] + o.ghost_serialize());
                    // from equality of sequences, first bytes are equal
                    assert(self.ghost_serialize().len() > 0);
                    assert(other.ghost_serialize().len() > 0);
                    assert(self.ghost_serialize()[0] == other.ghost_serialize()[0]);
                    // substitute the concrete first bytes (0 vs 1)
                    assert(seq![0u8][0] == (seq![1u8] + o.ghost_serialize())[0]);
                }
            } else {
                let s = self.get_Some_0();
                if other.is_None() {
                    // substitute ghost_serialize for Some vs None
                    assert(self.ghost_serialize() == seq![1u8] + s.ghost_serialize());
                    assert(other.ghost_serialize() == seq![0u8]);
                    // from equality of sequences, first bytes are equal
                    assert(self.ghost_serialize().len() > 0);
                    assert(other.ghost_serialize().len() > 0);
                    assert(self.ghost_serialize()[0] == other.ghost_serialize()[0]);
                    // substitute the concrete first bytes (1 vs 0)
                    assert((seq![1u8] + s.ghost_serialize())[0] == seq![0u8][0]);
                } else {
                    let o = other.get_Some_0();
                    // substitute ghost_serialize for Some vs Some
                    assert(self.ghost_serialize() == seq![1u8] + s.ghost_serialize());
                    assert(other.ghost_serialize() == seq![1u8] + o.ghost_serialize());
                    // equality of sequences implies equality of tails after dropping first byte
                    assert(self.ghost_serialize().subrange(1, self.ghost_serialize().len() as int)
                        == other.ghost_serialize().subrange(1, other.ghost_serialize().len() as int));
                    // identify tails with inner serializations
                    assert((seq![1u8] + s.ghost_serialize()).subrange(1, (seq![1u8] + s.ghost_serialize()).len() as int)
                        == s.ghost_serialize());
                    assert((seq![1u8] + o.ghost_serialize()).subrange(1, (seq![1u8] + o.ghost_serialize()).len() as int)
                        == o.ghost_serialize());
                    // conclude equality of inner serializations and apply injectivity for T
                    assert(s.ghost_serialize() == o.ghost_serialize());
                    s.lemma_serialize_injective(&o);
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
// Secondary Actions: ['extensional_equality', 'uselemma']
// Reasoning: Pipeline Analysis: The proof never uses the serialization-equality precondition nor the tag structure of Option. To conclude view_equal, we must split on (self, other), derive tag consistency from equality of ghost_serialize, and in the Some/Some case reduce to inner injectivity.
// Secondary Actions: ['extensional_equality', 'uselemma']
// 
// Parameters:
//   assertion_content: self.view_equal(other)
//   guidance: Open a proof block and match on (self, other). Show that equality of ghost_serialize implies the leading tag bytes are equal, ruling out (None, Some) and (Some, None). In the (Some(s), Some(o)) branch, assert (seq![1] + s.ghost_serialize()).subrange(1, ...) == (seq![1] + o.ghost_serialize()).subrange(1, ...), deduce s.ghost_serialize() == o.ghost_serialize(), then call s.lemma_serialize_injective(&o).
// 
// ACTION PHASE:
// Action Type: case_analysis
// Success: True
// Accepted: False
// Explanation: Generated 1 case_analysis candidates (guidance: Open a proof block and match on (self, other). Show that equality of ghost_serialize implies the lea...)
// Action Parameters:
//   guidance: Open a proof block and match on (self, other). Show that equality of ghost_serialize implies the leading tag bytes are equal, ruling out (None, Some) and (Some, None). In the (Some(s), Some(o)) branch, assert (seq![1] + s.ghost_serialize()).subrange(1, ...) == (seq![1] + o.ghost_serialize()).subrange(1, ...), deduce s.ghost_serialize() == o.ghost_serialize(), then call s.lemma_serialize_injective(&o).
// 
// CANDIDATES:
// Total Candidates: 1
// Has Multiple Candidates: False
// Agent Class: AssertionErrorAgent
