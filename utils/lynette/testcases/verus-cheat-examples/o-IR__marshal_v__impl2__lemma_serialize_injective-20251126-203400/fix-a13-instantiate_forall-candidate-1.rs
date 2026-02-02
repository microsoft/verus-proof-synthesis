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

impl<T: Marshalable> Marshalable for Vec<T> {
    open spec fn view_equal(&self, other: &Self) -> bool {
        let s = self@;
        let o = other@;
        s.len() == o.len() && (forall|i: int|
            0 <= i < s.len() ==> #[trigger] s[i].view_equal(&o[i]))
    }

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
    proof fn lemma_serialize_injective(self: &Self, other: &Self) {
        unimplemented!()
    }
}

impl Marshalable for Vec<u8> {
    open spec fn view_equal(&self, other: &Self) -> bool {
        self@ === other@
    }

    open spec fn is_marshalable(&self) -> bool {
        self@.len() <= usize::MAX && (self@.len() as usize).ghost_serialize().len()
            + self@.len() as int <= usize::MAX
    }

    open spec fn ghost_serialize(&self) -> Seq<u8> {
        (self@.len() as usize).ghost_serialize() + self@
    }

    proof fn lemma_serialize_injective(self: &Self, other: &Self) {
        assert(self.view_equal(other)) by {
            // Unfold view_equal to sequence equality on the views
            let s = self@;
            let o = other@;

            assert(s =~= o) by {
                // Step 1: Establish length equality via equality of serialized bytes
                let p1 = (s.len() as usize).ghost_serialize();
                let p2 = (o.len() as usize).ghost_serialize();

                // Both length prefixes have the same (fixed) length
                let x1: u64 = (s.len() as usize) as u64;
                let x2: u64 = (o.len() as usize) as u64;
                // Relate p1 and p2 to the u64 serialization lengths via open specs
                assert(p1 == x1.ghost_serialize());
                assert(p2 == x2.ghost_serialize());
                assert(x1.ghost_serialize() == spec_u64_to_le_bytes(x1));
                assert(x2.ghost_serialize() == spec_u64_to_le_bytes(x2));
                // Directly assert the fixed-length property for these concrete values
                assert forall |x: u64| spec_u64_to_le_bytes(x).len() == 8 by {
                    assert(spec_u64_to_le_bytes(x).len() == 8);
                };
                assert(spec_u64_to_le_bytes(x1).len() == 8);
                assert(spec_u64_to_le_bytes(x2).len() == 8);
                // Derive equal lengths from the equalities above
                assert(p1.len() == x1.ghost_serialize().len());
                assert(p2.len() == x2.ghost_serialize().len());
                assert(x1.ghost_serialize().len() == spec_u64_to_le_bytes(x1).len());
                assert(x2.ghost_serialize().len() == spec_u64_to_le_bytes(x2).len());
                assert(p1.len() == 8);
                assert(p2.len() == 8);
                assert(p1.len() == p2.len());

                // Connect ghost_serialize to the explicit concatenations
                assert(self.ghost_serialize() == p1 + s);
                assert(other.ghost_serialize() == p2 + o);
                assert(self.ghost_serialize() == other.ghost_serialize());

                // From equality of concatenations, deduce total lengths equal
                assert((p1 + s).len() == (p2 + o).len());
                // Concatenation length decomposes into sum of lengths
                assert((p1 + s).len() == p1.len() + s.len());
                assert((p2 + o).len() == p2.len() + o.len());
                // Hence the payload lengths are equal
                assert(s.len() == o.len());

                // Step 2: Prove element-wise equality
                assert forall |i: int| 0 <= i < s.len() implies s[i] == o[i] by {
                    let k = p1.len();
                    assert(k == p2.len());
                    // We have equality of the full serialized sequences
                    assert((p1 + s) == (p2 + o));
                    // Indices k + i are within bounds of both concatenations
                    assert(0 <= k + i && k + i < (p1 + s).len());
                    assert(0 <= k + i && k + i < (p2 + o).len());
                    // Indexing into concatenation past the prefix yields the payload elements
                    assert((p1 + s)[k + i] == s[i]);
                    assert((p2 + o)[k + i] == o[i]);
                    // Hence the i-th elements are equal
                    assert(s[i] == o[i]);
                };
            };
        }
    }
}

} // verus!

//Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1

// EVALUATION RESULT: Fix the target error by 1 without bandaid assertions

// 
// 
// ===== AGENT METADATA =====
// Agent Framework Information:
// 
// OBSERVATION PHASE:
// Error Location: (135, 135)
// Error Type: AssertFail
// Error Text:                 assert(spec_u64_to_le_bytes(x1).len() == 8);
// 
// REASONING PHASE:
// Primary Action: instantiate_forall
// Secondary Actions: ['add_trigger_assert']
// Reasoning: Pipeline Analysis: The verifier does not know the fixed-length property of the u64 little-endian serialization; it needs a universally quantified fact that spec_u64_to_le_bytes(x).len() == 8 for arbitrary x.
// Secondary Actions: ['add_trigger_assert']
// 
// Parameters:
//   assertion_content: spec_u64_to_le_bytes(x1).len() == 8
//   guidance: Introduce a universal assertion: assert forall |x: u64| spec_u64_to_le_bytes(x).len() == 8 by {  }; then immediately instantiate it for x1 and x2 to derive spec_u64_to_le_bytes(x1).len() == 8 and spec_u64_to_le_bytes(x2).len() == 8.
// 
// ACTION PHASE:
// Action Type: instantiate_forall
// Success: True
// Accepted: False
// Explanation: Generated 1 instantiate_forall candidates (guidance: Introduce a universal assertion: assert forall |x: u64| spec_u64_to_le_bytes(x).len() == 8 by {  }; ...)
// Action Parameters:
//   guidance: Introduce a universal assertion: assert forall |x: u64| spec_u64_to_le_bytes(x).len() == 8 by {  }; then immediately instantiate it for x1 and x2 to derive spec_u64_to_le_bytes(x1).len() == 8 and spec_u64_to_le_bytes(x2).len() == 8.
// 
// CANDIDATES:
// Total Candidates: 1
// Has Multiple Candidates: False
// Agent Class: AssertionErrorAgent
