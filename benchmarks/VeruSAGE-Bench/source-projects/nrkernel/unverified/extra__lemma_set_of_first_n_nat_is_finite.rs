use vstd::prelude::*;

fn main() {}

verus!{

// File: extra.rs
pub proof fn lemma_set_of_first_n_nat_is_finite( n: nat, )
    ensures Set::new(|i: nat| i < n).finite()
{   
}


}
