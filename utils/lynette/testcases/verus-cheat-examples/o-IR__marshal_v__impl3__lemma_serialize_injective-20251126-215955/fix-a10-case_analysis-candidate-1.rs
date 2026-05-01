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
                    // view_equal(None, None) == true
                    assert(true);
                } else {
                    let o = other.get_Some_0();
                    // ghost_serialize(None) == [0], ghost_serialize(Some(o)) == [1] ++ o.ghost_serialize()
                    assert(self.ghost_serialize() == seq![0u8]);
                    assert(other.ghost_serialize() == seq![1u8] + o.ghost_serialize());
                    // lengths are > 0 so index 0 is valid
                    assert(self.ghost_serialize().len() > 0);
                    assert(other.ghost_serialize().len() > 0);
                    // equality implies equality of first elements
                    assert(self.ghost_serialize()[0] == other.ghost_serialize()[0]);
                    // but first bytes are 0 vs 1, contradiction
                    assert(seq![0u8][0] != (seq![1u8] + o.ghost_serialize())[0]);
                    assert(false);
                }
            } else {
                let s = self.get_Some_0();
                if other.is_None() {
                    // ghost_serialize(Some(s)) == [1] ++ s.ghost_serialize(), ghost_serialize(None) == [0]
                    assert(self.ghost_serialize() == seq![1u8] + s.ghost_serialize());
                    assert(other.ghost_serialize() == seq![0u8]);
                    // lengths are > 0 so index 0 is valid
                    assert(self.ghost_serialize().len() > 0);
                    assert(other.ghost_serialize().len() > 0);
                    // equality implies equality of first elements
                    assert(self.ghost_serialize()[0] == other.ghost_serialize()[0]);
                    // but first bytes are 1 vs 0, contradiction
                    assert((seq![1u8] + s.ghost_serialize())[0] != seq![0u8][0]);
                    assert(false);
                } else {
                    let o = other.get_Some_0();
                    // expand serializations with leading tag 1
                    assert(self.ghost_serialize() == seq![1u8] + s.ghost_serialize());
                    assert(other.ghost_serialize() == seq![1u8] + o.ghost_serialize());
                    // strip the first byte to get equality of tails
                    assert(self.ghost_serialize().subrange(1, self.ghost_serialize().len() as int)
                        == other.ghost_serialize().subrange(1, other.ghost_serialize().len() as int));
                    // identify tails with inner serializations
                    assert((seq![1u8] + s.ghost_serialize()).subrange(1, (seq![1u8] + s.ghost_serialize()).len() as int)
                        == s.ghost_serialize());
                    assert((seq![1u8] + o.ghost_serialize()).subrange(1, (seq![1u8] + o.ghost_serialize()).len() as int)
                        == o.ghost_serialize());
                    // conclude equality of inner serializations
                    assert(s.ghost_serialize() == o.ghost_serialize());
                    // inner values are marshalable from Option.is_marshalable() under the preconditions
                    assert(s.is_marshalable());
                    assert(o.is_marshalable());
                    // apply injectivity of T
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
// Secondary Actions: ['uselemma', 'seqsetmap']
// Reasoning: Pipeline Analysis: The assertion self.view_equal(other) is made without leveraging the preconditions (marshalable and equal serializations) and without analyzing Option’s tag-based serialization. We must split on (self, other), use the first byte (0 vs 1) to rule out cross-cases, and in Some/Some reduce to inner equality and apply T’s injectivity.
// Secondary Actions: ['uselemma', 'seqsetmap']
// 
// Parameters:
//   assertion_content: self.view_equal(other)
//   guidance: Match on (self, other). For (None, None) return true. For (None, Some(_)) and (Some(_), None), use ghost_serialize equality and compare index 0 to show 0 != 1, contradicting equality. For (Some(s), Some(o)), from equality of ghost_serialize, strip the first byte to get s.ghost_serialize() == o.ghost_serialize(); use marshalable preconditions to call s.lemma_serialize_injective(&o) and conclude s.view_equal(o).
// 
// ACTION PHASE:
// Action Type: case_analysis
// Success: True
// Accepted: False
// Explanation: Generated 1 case_analysis candidates (guidance: Match on (self, other). For (None, None) return true. For (None, Some(_)) and (Some(_), None), use g...)
// Action Parameters:
//   guidance: Match on (self, other). For (None, None) return true. For (None, Some(_)) and (Some(_), None), use ghost_serialize equality and compare index 0 to show 0 != 1, contradicting equality. For (Some(s), Some(o)), from equality of ghost_serialize, strip the first byte to get s.ghost_serialize() == o.ghost_serialize(); use marshalable preconditions to call s.lemma_serialize_injective(&o) and conclude s.view_equal(o).
// 
// CANDIDATES:
// Total Candidates: 1
// Has Multiple Candidates: False
// Agent Class: AssertionErrorAgent
