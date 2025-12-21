use vstd::prelude::*;

use vstd::std_specs::bits::u64_leading_zeros;
fn main() {}

verus! {

/*
Definitions from vstd
-----
vstd::std_specs::bits
-----
#[verifier::opaque]
pub open spec fn u64_leading_zeros(i: u64) -> int
    decreases i,
{
    if i == 0 {
        64
    } else {
        u64_leading_zeros(i / 2) - 1
    }
}
-----
*/

#[verifier::external_body]
proof fn leading_zeros_monotonic(w:u64)
    ensures
       forall |x:u64| x < w ==> u64_leading_zeros(w) <= u64_leading_zeros(x),
    decreases w,
	{
		unimplemented!()
	}

proof fn leading_zeros_between(lo:u64, mid:u64, hi:u64)
    requires lo <= mid < hi,
    ensures u64_leading_zeros(lo) >= u64_leading_zeros(mid) >= u64_leading_zeros(hi),
{
}

}
