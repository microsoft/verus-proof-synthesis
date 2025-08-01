use vstd::prelude::*;
fn main() {}

verus!{
    proof fn lemma_seq_filter_subrange<T>(v: Seq<T>, i: int, pred: FnSpec(T) -> bool)
        requires
            0 <= i <= v.len(),
        ensures
            v.filter(pred) == v.subrange(0, i).filter(pred) + v.subrange(i, ( v.len() ) as int).filter(pred),
    {
        assert(v.filter(pred) =~= v.subrange(0, i).filter(pred) + v.subrange(i, ( v.len() ) as int).filter(pred));
    }

    pub fn myfun4(x: &Vec<u64>, y: &mut Vec<u64>)
    requires 
        old(y).len() == 0,
    ensures 
        y@ == x@.filter(|k:u64| k % 3 == 0),
    {
        let mut i: usize = 0;
        let xlen = x.len();

        assert(y@ == Seq::empty());

        while (i < xlen) 
            invariant
                i <= xlen,
                y@ == x@.subrange(0, i as int).filter(|k:u64| k % 3 == 0),
        { 
            if (x[i] % 3 == 0) {
                y.push(x[i]);            
            }
            i = i + 1;

            proof {
                lemma_seq_filter_subrange(x@, i as int, |k:u64| k % 3 == 0);
                assert(y@ == x@.subrange(0, i as int).filter(|k:u64| k % 3 == 0));
            }
        }

        proof {
            lemma_seq_filter_subrange(x@, xlen as int, |k:u64| k % 3 == 0);
            assert(x@.subrange(0, xlen as int) == x@);
        }
    }
}



// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1