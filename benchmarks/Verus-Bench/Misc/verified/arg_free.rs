use vstd::prelude::*;
fn main() {}

verus!{
fn choose_odd()
{
    let mut idx: u64 = 0;
    let mut res: u64 = 5;
    
    let ghost gap = res-idx;
    
    while (idx < 10)
    invariant
        idx<=10,
        gap<100,
        gap==res-idx,
    {
        res = res + 1;
        idx = idx + 1;
    }
    idx = 0;
    
    let ghost gap = res - idx;
   
    while (idx < 10)
    invariant
        idx<=10,
        gap<100,
        gap==res-idx,
    {
        
        res = res + 1;
        idx = idx + 1;
        
    }
    assert(res == 25);
}
}
