use vstd::prelude::*;

fn main() {}

verus!{

// File: src/properties.rs
pub trait SpecCombinator {
    type Type;

    spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>;

}

pub trait SecureSpecCombinator : SpecCombinator {}

// File: src/regular/repetition.rs
pub struct RepeatN<C>(pub C, pub usize);

impl<C: View> View for RepeatN<C> {
    type V = RepeatN<<C as View>::V>;

    open spec fn view(&self) -> Self::V {
        RepeatN(self.0@, self.1)
    }

}

impl<C: SecureSpecCombinator> SpecCombinator for RepeatN<C> {
    type Type = Seq<C::Type>;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> {
        self.spec_parse_helper(s, self.1)
    }

}



impl<C: SecureSpecCombinator> RepeatN<C> {

    pub closed spec fn spec_parse_helper(&self, s: Seq<u8>, n: usize) -> Option<(int, Seq<C::Type>)>
        decreases n,
    {
        if n == 0 {
            Some((0, seq![]))
        } else {
            match self.spec_parse_helper(s, (n - 1) as usize) {
                Some((m, vs)) => match self.0.spec_parse(s.skip(m as int)) {
                    Some((k, v)) => Some((m + k, vs.push(v))),
                    None => None,
                },
                None => None,
            }
        }
    }

    proof fn lemma_spec_parse_err_unrecoverable(&self, s: Seq<u8>, n1: usize, n2: usize)
        ensures
            n1 <= n2 ==> self.spec_parse_helper(s, n1) is None ==> self.spec_parse_helper(
                s,
                n2,
            ) is None,
        decreases n2,
    {
        if n2 == n1 {
        } else if n2 > n1 {
            self.lemma_spec_parse_err_unrecoverable(s, n1, (n2 - 1) as usize);
        }
    }

}


}
