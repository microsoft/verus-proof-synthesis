

use vstd::prelude::*;

fn main() {}

verus! {

    proof fn lemma_seq_subrange_ascend<T>(v: Seq<T>, i: int, j: int)
        requires
            0 <= i < j <= v.len(),
        ensures
            v.subrange(i, j).drop_last() == v.subrange(i, j - 1),
    {
        assert(v.subrange(i, j).drop_last() == v.subrange(i, j - 1));
    }

    proof fn lemma_seq_subrange_all<T>(v: Seq<T>)
        ensures
            v == v.subrange(0, v.len()),
    {
        assert(v == v.subrange(0, v.len()));
    }

    #[verifier::loop_isolation(false)]

    fn is_non_prime(n: u64) -> (result: bool)
        requires
            n >= 2,
        ensures
            result == (exists|k: int| 2 <= k < n && is_divisible(n as int, k)),
    {
        if n <= 1 {
            return true;
        }
        let mut index = 2;

        // Loop invariant block
        while (index < n)
            invariant
                2 <= index < n,
                index < n,
                n >= 2,
                // Additional conditions based on the analysis
                (index <= sqrt(n as u64) + 1) || (n as u64 < 4),
                !(n as u64 % index as u64 == 0),
        {
            if ((n % index) == 0) {
                return true;
            }
            index += 1;
        }
        false
    }

} // verus!
// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1