use vstd::prelude::*;

fn main() {}

verus!{

// File: array.rs
pub struct Array<A, const N: usize>{
    pub seq: Ghost<Seq<A>>,
    pub ar: [A;N]
}

impl<A, const N: usize> Array<A, N> {

    #[verifier(inline)]
    pub open spec fn view(&self) -> Seq<A>{
        self.seq@
    }

    pub open spec fn wf(&self) -> bool{
        self.seq@.len() == N
    }

}



// File: array_vec.rs
pub struct ArrayVec<T, const N: usize> {
    pub data: Array<T, N>,
    pub len: usize,
}

impl<T: Copy, const N: usize> ArrayVec<T, N> {

    #[verifier(when_used_as_spec(spec_len))]
    pub fn len(&self) -> (ret: usize)
        requires
            self.wf(),
        ensures
            ret == self.spec_len(),
    {
        self.len
    }


    pub open spec fn spec_len(&self) -> usize {
        self.len
    }

    #[verifier(when_used_as_spec(spec_capacity))]
    pub const fn capacity(&self) -> (ret: usize)
        ensures
            ret == self.spec_capacity(),
    {
        N
    }


    pub open spec fn spec_capacity(&self) -> usize {
        N
    }

    pub open spec fn view(&self) -> Seq<T>
        recommends self.wf(),
    {
        self.view_until(self.len() as nat)
    }

    pub open spec fn view_until(&self, len: nat) -> Seq<T>
        recommends
            0 <= len <= self.len() as nat,
    {
        self.data@.subrange(0,len as int)
    }

    pub open spec fn wf(&self) -> bool {
        &&& 0 <= N <= usize::MAX
        &&& self.len() <= self.capacity()
        &&& self.data.wf()
    }

	#[verifier::external_body]
    pub fn pop(&mut self) -> (ret: T)
        requires
            old(self).wf(),
            old(self).len() > 0,
        ensures
            self.wf(),
            self.len() == old(self).len() - 1,
            ret == old(self)@[old(self).len() - 1],
            self@ =~= old(self)@.drop_last(),
	{
		unimplemented!()
	}

}


fn test<const N: usize>(ar: &mut ArrayVec<u64, N>)
requires
    old(ar).wf(),
    old(ar).len() == 1,
    old(ar)@[0] == 0,
    N == 2,

{
    let v_0 = ar.pop();
    assert(ar@ == Seq::<u64>::empty());
    assert(v_0 == 0);
}


}
