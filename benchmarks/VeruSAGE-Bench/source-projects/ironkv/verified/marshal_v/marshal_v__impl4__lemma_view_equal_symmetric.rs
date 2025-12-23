use vstd::prelude::*;

fn main() {}

verus!{

// File: marshal_v.rs
pub trait Marshalable : Sized {

  spec fn view_equal(&self, other: &Self) -> bool;

	#[verifier::external_body]
  proof fn lemma_view_equal_symmetric(&self, other: &Self)
    ensures self.view_equal(other) == other.view_equal(self)
  {unimplemented!()}

}


impl Marshalable for usize {

  open spec fn view_equal(&self, other: &Self) -> bool {
    self@ === other@
  }

	#[verifier::external_body]
  proof fn lemma_view_equal_symmetric(&self, other: &Self)
	{
		unimplemented!()
	}

}


impl Marshalable for Vec<u8> {

  open spec fn view_equal(&self, other: &Self) -> bool {
    self@ === other@
  }

	#[verifier::external_body]
  proof fn lemma_view_equal_symmetric(&self, other: &Self)
	{
		unimplemented!()
	}

}


impl<T: Marshalable> Marshalable for Vec<T> {

  open spec fn view_equal(&self, other: &Self) -> bool {
    let s = self@;
    let o = other@;
    s.len() == o.len() && (forall |i: int| 0 <= i < s.len() ==> #[trigger] s[i].view_equal(&o[i]))
  }

  #[verifier::spinoff_prover]
  proof fn lemma_view_equal_symmetric(&self, other: &Self)
    // req, ens from trait
  {
    let s = self@;
    let o = other@;
    if self.view_equal(other) {
      assert forall |i: int| 0 <= i < o.len() implies #[trigger] o[i].view_equal(&s[i]) by {
        s[i].lemma_view_equal_symmetric(&o[i]);
      }
    } else {
      if s.len() != o.len() {
        // trivial
      } else {
        let i = choose |i: int| 0 <= i < s.len() && ! #[trigger] s[i].view_equal(&o[i]);
        s[i].lemma_view_equal_symmetric(&o[i]);
      }
    }
  }

}



}
