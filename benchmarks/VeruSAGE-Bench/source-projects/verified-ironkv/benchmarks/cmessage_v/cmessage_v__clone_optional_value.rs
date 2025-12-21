use vstd::prelude::*;

fn main() {}


verus! {

	#[verifier::external_body]
pub fn clone_vec_u8(v: &Vec<u8>) -> (out: Vec<u8>)
ensures
    out@ == v@
	{
		unimplemented!()
	}

pub open spec fn optional_value_view(ov: Option::<Vec::<u8>>) -> Option::<Seq::<u8>>
{
    match ov {
        Some(v) => Some(v@),
        None => None,
    }
}

pub fn clone_optional_value(ov: &Option::<Vec::<u8>>) -> (res: Option::<Vec::<u8>>)
    ensures optional_value_view(*ov) == optional_value_view(res)
{
    match ov.as_ref() {
        Some(v) => Some(clone_vec_u8(v)),
        None => None,
    }
}

}
