use vstd::prelude::*;
use vstd::set_lib::lemma_len_subset;

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



// File: array_set.rs
pub struct ArraySet<const N: usize> {
    pub data: Array<bool, N>,
    pub len: usize,

    pub set: Ghost<Set<usize>>,
}

impl <const N: usize> ArraySet<N> {

    pub closed spec fn view(&self) -> Set<usize>{
        self.set@
    }

    pub closed spec fn wf(&self) -> bool{
        &&&
        self.data.wf()
        &&&
        self.set@.finite()
        &&&
        0 <= self.len <= N
        &&&
        forall|i:usize| 
            #![trigger self.data@[i as int]]
            #![trigger self.set@.contains(i)]
            0 <= i < N && self.data@[i as int] ==> self.set@.contains(i)
        &&&
        forall|i:usize| 
            #![trigger self.data@[i as int]]
            #![trigger self.set@.contains(i)]
            self.set@.contains(i) ==> 0 <= i < N && self.data@[i as int]     
        &&&
        self.len == self.set@.len() 
    }

    pub fn insert(&mut self, v:usize)
        requires
            old(self).wf(),
            old(self)@.contains(v) == false,
            0 <= v < N,
        ensures
            self.wf(),
            self@ == old(self)@.insert(v),
    {
        self.data.set(v, true);
        self.set = Ghost(self.set@.insert(v));
        proof{
            let all_value_set = Set::new(|v: usize| 0 <= v < N);
            assume(all_value_set.finite());
            assume(all_value_set.len() == N); // this should be inferred smh by verus...
            assert(
                forall|v: usize| #![auto]
                    self.set@.contains(v) 
                    ==>
                    all_value_set.contains(v)
            );
            lemma_len_subset::<usize>(self.set@, all_value_set);
            assert(self.set@.len() <= N);
        }
        self.len = self.len + 1;
    }

}



}
