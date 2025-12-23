#[allow(unused_imports)]
use vstd::prelude::*;

fn main() {}

verus! {

spec fn my_recursive_spec(i: nat) -> nat
    decreases i
{
    if i == 0 {
        0
    } else {
        10 + my_recursive_spec( (i - 1) as nat)
    }
}

proof fn lemma_monotonic(i: nat, j:nat)
    requires
        i <= j,
    ensures
        my_recursive_spec(i) <= my_recursive_spec(j),
    decreases j
{
    if i < j {
        lemma_monotonic(i, (j-1) as nat);
    }
}

fn my_fun(n: u64) -> (sum: u64)
    requires
        my_recursive_spec(n as nat) < 10000,
    ensures
        my_recursive_spec(n as nat) == sum,
{
    let mut i: u64 = 0;
    let mut sum: u64 = 0;
    while i < n
        invariant
            sum == my_recursive_spec(i as nat),
            my_recursive_spec(n as nat) < 10000,
            i <= n,
    {
        i = i + 1;

        assert(sum + 10 <=my_recursive_spec(n as nat)) by{
            lemma_monotonic(i as nat, n as nat);
        }

        sum = sum + 10;
    }
    sum
}


}
