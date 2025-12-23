use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(N: usize) -> (ret: usize)
    requires
        0 < N < 10000,
    ensures
        ret == 2 * N,
{
    let mut i: usize = 0;
    let mut sum: usize = 10000;

    while (i < N)
        invariant
            N < 10000,
            i <= N,
            sum == 2*i,
    {
        if i == 0 {
            sum = 2;
        }
        else{
            sum = sum + 2;
        }
        i = i + 1;
    }

    sum

}
}
