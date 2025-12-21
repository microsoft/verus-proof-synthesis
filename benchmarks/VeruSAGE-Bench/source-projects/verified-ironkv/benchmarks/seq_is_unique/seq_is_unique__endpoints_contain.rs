use vstd::prelude::*;

fn main() {}

verus! {
pub struct AbstractEndPoint {
    pub id: Seq<u8>,
}

// #[derive(Copy, Clone)]
#[derive(PartialEq, Eq, Hash)]
pub struct EndPoint {
    pub id: Vec<u8>,
}

impl EndPoint {

    pub open spec fn view(self) -> AbstractEndPoint {
        AbstractEndPoint{id: self.id@}
    }
}


pub open spec fn abstractify_end_points(end_points: Vec<EndPoint>) -> Seq<AbstractEndPoint>
{
    end_points@.map(|i, end_point: EndPoint| end_point@)
}


    #[verifier::external_body]
pub fn do_end_points_match(e1: &EndPoint, e2: &EndPoint) -> (eq: bool)
    ensures
eq == (e1@ == e2@)
{
    unimplemented!()
}

    pub fn endpoints_contain(endpoints: &Vec<EndPoint>, endpoint: &EndPoint) -> (present: bool)
ensures present == abstractify_end_points(*endpoints).contains(endpoint@)
    {
        let mut j: usize = 0;
        while j < endpoints.len()
            invariant
                0 <= j && j <= endpoints.len(),
                forall |k: int| #![trigger endpoints@[k]@] 0 <= k && k < j ==> endpoint@ != endpoints@[k]@,
                decreases
                    endpoints.len() - j
                    {
                        if do_end_points_match(endpoint, &endpoints[j]) {
                            assert (abstractify_end_points(*endpoints)[j as int] == endpoint@);
                            return true;
                        }
                        j = j + 1;
                    }
        return false;
    }

}
