use vstd::prelude::*;
use vstd::std_specs::bits::u64_leading_zeros;

fn main() {}

verus! {

proof fn leading_zeros_monotonic(w:u64)
    ensures
       forall |x:u64| x < w ==> u64_leading_zeros(w) <= u64_leading_zeros(x),
    decreases w,
{
    if w == 0 {
    } else {
        reveal(u64_leading_zeros);
        assert forall |x:u64| x < w implies u64_leading_zeros(w) <= u64_leading_zeros(x) by {
            leading_zeros_monotonic(w / 2);
            if x < w / 2 {

            } else {
                assert(x / 2 <= w / 2);
                if (x / 2 < w / 2) {
                    assert(u64_leading_zeros(w/2) <= u64_leading_zeros(x/2));
                } else {
                }
            }
        }
    }
}

}
