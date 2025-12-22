use vstd::prelude::*;

use vstd::raw_ptr::*;
use vstd::*;
use vstd::layout::*;

fn main() {}

verus! {

pub proof fn mul_mod_right(a: int, b: int)
    requires b != 0,
    ensures (a * b) % b == 0,
{
}

}
