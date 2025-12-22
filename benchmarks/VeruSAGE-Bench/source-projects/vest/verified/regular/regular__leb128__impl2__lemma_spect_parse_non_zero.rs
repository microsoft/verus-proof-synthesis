use vstd::prelude::*;

fn main() {}

verus!{


// File: src/regular/sequence.rs
pub type GhostFn<I, O> = spec_fn(I) -> O;

pub type SpecPair<Fst, Snd> = Pair<Fst, Snd, GhostFn<<Fst as SpecCombinator>::Type, Snd>>;

impl<Fst, Snd> SpecCombinator for SpecPair<Fst, Snd> where 
    Fst: SecureSpecCombinator,
    Snd: SpecCombinator,
 {
    type Type = (Fst::Type, Snd::Type);

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> {
        if let Some((n, v1)) = self.fst.spec_parse(s) {
            let snd = (self.snd)(v1);
            if let Some((m, v2)) = snd.spec_parse(s.skip(n as int)) {
                Some((n + m, (v1, v2)))
            } else {
                None
            }
        } else {
            None
        }
    }

}


pub struct Pair<Fst, Snd, Cont> {
    /// combinators that contain dependencies
    pub fst: Fst,
    // _snd: std::marker::PhantomData<Snd>,
    /// phantom data representing the second combinator
    /// (it really should be private, but this is a workaround for Verus's
    /// conservative treatment of opaque types, which doesn't allow field access
    /// of opaque types in open spec functions)
    pub _snd: std::marker::PhantomData<Snd>,
    /// closure that captures dependencies and maps them to the dependent combinators
    pub snd: Cont,
}

impl<Fst, Snd> Pair<Fst, Snd, GhostFn<Fst::Type, Snd>> where 
    Fst: SecureSpecCombinator,
    Snd: SpecCombinator,
{

    pub open spec fn spec_new(fst: Fst, snd: GhostFn<Fst::Type, Snd>) -> Self {
        Pair { fst, _snd: std::marker::PhantomData, snd }
    }

}


impl<Fst, Snd, Cont> View for Pair<Fst, Snd, Cont> where
    Fst: View,
    Snd: View,
    Cont: View<V = GhostFn<<Fst::V as SpecCombinator>::Type, Snd::V>>,
    Fst::V: SecureSpecCombinator,
    Snd::V: SpecCombinator,
 {
    type V = Pair<Fst::V, Snd::V, GhostFn<<Fst::V as SpecCombinator>::Type, Snd::V>>;

    open spec fn view(&self) -> Self::V {
        Pair::spec_new(self.fst@, self.snd@)
    }

}


impl<Fst: SecureSpecCombinator, Snd: SpecCombinator> SpecCombinator for (Fst, Snd) {
    type Type = (Fst::Type, Snd::Type);

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> {
        Pair::spec_new(self.0, |r: Fst::Type| self.1).spec_parse(s)
    }

}



// File: src/properties.rs
pub trait SpecCombinator {
    type Type;

    spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>;

}


impl<C: SpecCombinator> SpecCombinator for &C {
    type Type = C::Type;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> {
        (*self).spec_parse(s)
    }

}


impl<C: SpecCombinator> SpecCombinator for Box<C> {
    type Type = C::Type;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> {
        (**self).spec_parse(s)
    }

}



pub trait SecureSpecCombinator : SpecCombinator {}

// File: src/regular/leb128.rs
pub struct UnsignedLEB128;

pub type UInt = u64;

impl View for UnsignedLEB128 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        Self
    }

}

#[allow(unused_macros)]
macro_rules! uint_size { () => { 8 } }

#[allow(unused_macros)]
macro_rules! is_high_8_bit_set {
    ($v:expr) => { $v as u8 >= 0x80 };
}

#[allow(unused_macros)]
macro_rules! take_low_7_bits {
    ($v:expr) => { $v as u8 & 0x7f };
}

#[allow(unused_macros)]
macro_rules! set_high_8_bit {
    ($v:expr) => {
        ($v | 0x80) as u8
    };
}

#[allow(unused_macros)]
macro_rules! n_bit_max_unsigned {
    ($n:expr) => { if $n == 0 { 0 } else { UInt::MAX >> (((8 * uint_size!()) - $n) as usize) } }
}

impl SpecCombinator for UnsignedLEB128 {
    type Type = UInt;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
        decreases s.len(),
    {
        let v = take_low_7_bits!(s.first());

        if s.len() != 0 {
            if is_high_8_bit_set!(s.first()) {
                match self.spec_parse(s.drop_first()) {
                    Some(
                        (n, v2),
                    ) =>
                    // Check for overflow and canonicity (v2 should not be 0)
                    if n < usize::MAX && 0 < v2 <= n_bit_max_unsigned!(8 * uint_size!() - 7) {
                        Some((n + 1, v2 << 7 | v as Self::Type))
                    } else {
                        None
                    },
                    None => None,
                }
            } else {
                Some((1, v as Self::Type))
            }
        } else {
            None
        }
    }

}


impl UnsignedLEB128 {

    proof fn lemma_spec_parse_non_zero(&self, s: Seq<u8>)
        requires
            ({
                let s0 = s[0];
                is_high_8_bit_set!(s0)
            }),
        ensures
            self.spec_parse(s) matches Some((_, x)) ==> x > 1,
    {
        if let Some((_, x)) = self.spec_parse(s) {
            let (_, rest) = self.spec_parse(s.drop_first()).unwrap();
            let s0 = s[0];

            assert(0 < rest <= n_bit_max_unsigned!(8 * uint_size!() - 7) ==> rest << 7
                | take_low_7_bits!(s0) as UInt > 1) by (bit_vector);
        }
    }

}



}
