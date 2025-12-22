use vstd::prelude::*;
fn main() {}
verus! {

pub struct AbstractEndPoint {
    pub id: Seq<u8>,
}

#[derive(PartialEq, Eq, Hash)]
pub struct EndPoint {
    pub id: Vec<u8>,
}

impl EndPoint {
    pub open spec fn view(self) -> AbstractEndPoint {
        AbstractEndPoint { id: self.id@ }
    }
}

pub open spec fn abstractify_end_points(end_points: Vec<EndPoint>) -> Seq<AbstractEndPoint> {
    end_points@.map(|i, end_point: EndPoint| end_point@)
}

#[verifier::opaque]
pub open spec fn seq_is_unique<T>(s: Seq<T>) -> bool {
    forall|i: int, j: int|
        #![trigger s[i], s[j]]
        0 <= i && i < s.len() && 0 <= j && j < s.len() && s[i] == s[j] ==> i == j
}

#[verifier::external_body]
pub fn do_end_points_match(e1: &EndPoint, e2: &EndPoint) -> (eq: bool)
    ensures
        eq == (e1@ == e2@),
{
    unimplemented!()
}

pub fn test_unique(endpoints: &Vec<EndPoint>) -> (unique: bool)
    ensures
        unique == seq_is_unique(abstractify_end_points(*endpoints)),
{
    let mut i: usize = 0;
    while i < endpoints.len() {
        let mut j: usize = 0;
        while j < endpoints.len() {
            if i != j && do_end_points_match(&endpoints[i], &endpoints[j]) {
                return false;
            }
            j = j + 1;
        }
        i = i + 1;
    };
    return true;
}

} // verus!
