use vstd::prelude::*;


fn main() {}

verus! {

pub proof fn sub_distribute(a: int, b: int, c: int)
    ensures a * c - b * c == (a - b) * c,
{
}

}
