use vstd::prelude::*;

fn main() {}

verus!{

// File: array.rs
pub struct Array<A, const N: usize>{
    pub seq: Ghost<Seq<A>>,
    pub ar: [A;N]
}

impl<A, const N: usize> Array<A, N> {

    #[verifier(external_body)]
    pub fn get(&self, i: usize) -> (out: &A)
        requires
            0 <= i < N,
            self.wf(),
        ensures
            *out == self.seq@[i as int],
	{
		unimplemented!()
	}

    #[verifier(inline)]
    pub open spec fn spec_index(self, i: int) -> A
        recommends self.seq@.len() == N,
                   0 <= i < N,
    {
        self.seq@[i]
    }

    pub open spec fn wf(&self) -> bool{
        self.seq@.len() == N
    }

}


impl<A, const N: usize> Array<A, N> {

    #[verifier(external_body)]
    pub fn set(&mut self, i: usize, out: A)
        requires
            0 <= i < N,
            old(self).wf(),
        ensures
            self.seq@ =~= old(self).seq@.update(i as int, out),
            self.wf(),
	{
		unimplemented!()
	}

}


fn test<const N: usize>(ar: &mut Array<u64, N>)
    requires
        old(ar).wf(),
        old(ar)[1] == 0,
        N == 2,

    {
    let v_1 = ar.get(1);
    assert(v_1 == 0);
    ar.set(0,1);
    let v_0 = ar.get(0);
    assert(v_0 == 1);
    let v_1_new = ar.get(1);
    // assert(v_1_new != 0); // this should fail
    }


}
