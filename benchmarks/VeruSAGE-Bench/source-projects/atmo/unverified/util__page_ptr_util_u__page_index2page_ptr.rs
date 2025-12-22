use vstd::prelude::*;

fn main() {}

verus!{

// File: lemma/lemma_t.rs
	#[verifier::external_body]
#[verifier(external_body)]
pub proof fn lemma_usize_u64(x: u64)
    ensures
        x as usize as u64 == x,
	{
		unimplemented!()
	}


// File: util/page_ptr_util_u.rs
pub open spec fn spec_page_index2page_ptr(i: usize) -> usize
    recommends
        page_index_valid(i),
{
    (i * 4096) as usize
}

#[verifier(when_used_as_spec(spec_page_index2page_ptr))]
pub fn page_index2page_ptr(i: usize) -> (ret: usize)
    requires
        0 <= i < NUM_PAGES,
    ensures
        ret == spec_page_index2page_ptr(i),
{
    i * 4096usize
}

pub open spec fn page_index_valid(index: usize) -> bool {
    (0 <= index < NUM_PAGES)
}


// File: define.rs
pub const NUM_PAGES: usize = 2 * 1024 * 1024;

pub const MAX_USIZE: u64 = 31 * 1024 * 1024 * 1024;


}
