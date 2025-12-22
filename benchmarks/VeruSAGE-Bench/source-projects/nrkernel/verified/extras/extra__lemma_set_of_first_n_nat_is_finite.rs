use vstd::prelude::*;

fn main() {}

verus!{

// File: extra.rs
pub proof fn lemma_set_of_first_n_nat_is_finite( n: nat, )
    requires
    ensures Set::new(|i: nat| i < n).finite()
    decreases n
{   
    let b = Set::new(|i: nat| i < n);
    if (n == 0) {    
        assert(Set::new(|i: nat| i < 0) === Set::empty());
        assert(Set::new(|i: nat| i < 0).finite());
    } else {
        lemma_set_of_first_n_nat_is_finite((n - 1) as nat);
        let c = Set::new(|i: nat| i < n - 1).insert((n - 1) as nat);
        assert(c.finite());
        assert(c === b);
        assert(b.finite());
    }
}


}
