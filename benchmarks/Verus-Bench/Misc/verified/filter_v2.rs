use vstd::prelude::*;
fn main() {}

verus!{

proof fn lemma_seq_take_ascend<T>(v: Seq<T>, i: int)
    requires
        0< i <= v.len(),
    ensures
        v.take(i as int).drop_last() == v.take(i-1),
{
    assert(v.take(i as int).drop_last()=~=v.take(i-1));
}

proof fn lemma_seq_take_all<T>(v: Seq<T>)
    ensures
        v == v.take(v.len() as int),
{
    assert(v =~= v.take(v.len() as int));
}

pub fn myfun4(x: &Vec<u64>, y: &mut Vec<u64>)
requires 
    old(y).len() == 0,
ensures 
    y@ == x@.filter(|k:u64| k%3 == 0),
{
    let mut i: usize = 0;
    let xlen = x.len();
    
    assert(y@ == x@.take(0).filter(|k:u64| k%3 ==0)); 
    while (i < xlen) 
        invariant 
            0 <= i <= xlen,
            x@.len() == xlen,  
            y@ == x@.take(i as int).filter(|k:u64| k%3 == 0),
    { 
        if (x[i] % 3 == 0) {
            y.push(x[i]);
            
        }
        proof{
            lemma_seq_take_ascend(x@, i+1);
            reveal(Seq::filter);//routine for filter
        }
        i = i + 1;
    }
    proof{
        lemma_seq_take_all(x@);
    }
}
}
