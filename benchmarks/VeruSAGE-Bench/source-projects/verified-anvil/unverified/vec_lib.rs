#[allow(unused_imports)]
use vstd::prelude::*;
use vstd::seq_lib::*;

fn main() {}

verus! {

trait VerusClone: View + Sized {
    fn verus_clone(&self) -> (r: Self)
        ensures self == r;
}

fn vec_filter<V: VerusClone + View + Sized>(v: Vec<V>, f: impl Fn(&V)->bool, f_spec: spec_fn(V)->bool) -> (r: Vec<V>)
    requires
        forall|v: V| #[trigger] f.requires((&v,)),
        forall |v:V,r:bool| f.ensures((&v,), r) ==> f_spec(v) == r,
    ensures r@.to_multiset() =~= v@.to_multiset().filter(f_spec)
{
    let mut r = Vec::new();
    let mut i = 0;
    for i in 0..v.len()
    {
        if f(&v[i]) {
            r.push(v[i].verus_clone());
        }
    }
    r

}

}
