use vstd::prelude::*;
fn main() {}

verus!{
    proof fn lemma_seq_subrange_ascend<T>(v: Seq<T>, i: int, j: int)
        requires
            0<= i < j <= v.len(),
        ensures
            v.subrange(i as int, j as int).drop_last() == v.subrange(i as int, j-1 ),
    {
        assert(v.subrange(i as int, j as int).drop_last() =~= v.subrange(i as int, j-1));
    }

    proof fn lemma_seq_subrange_all<T>(v: Seq<T>)
        ensures
            v == v.subrange(0, v.len() as int),
    {
        assert(v =~= v.subrange(0, v.len() as int));
    }

    #[verifier::loop_isolation(false)]

    pub fn myfun4(x: &Vec<u64>, y: &mut Vec<u64>)
    requires 
        old(y).len() == 0,
    ensures 
        y@ == x@.filter(|k:u64| k%3 == 0),
    {
        proof {
            reveal(Seq::filter);
        }

        let mut i: usize = 0;
        let xlen = x.len();
        
        assert(y@ == x@.subrange(0, (i) as int).filter(|k: u64| k%3 == 0));
        
        while (i < xlen)
            invariant
                i <= xlen,
                y@ == x@.subrange(0, (i) as int).filter(|k: u64| k%3 == 0),
        { 
            if (x[i] % 3 == 0) {
                y.push(x[i]);            
            }
            i = i + 1;

            proof {
                lemma_seq_subrange_ascend(x@, 0, i as int);
            }
        }

        proof {
            lemma_seq_subrange_all(x@);
        }
    }
}

// Score: (3, 0)
// Safe: True