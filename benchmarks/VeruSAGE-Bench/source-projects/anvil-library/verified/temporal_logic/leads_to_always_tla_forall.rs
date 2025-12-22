use vstd::prelude::*;
use vstd::map_lib::*;

fn main() {}

verus!{

// File: defs.rs
pub struct Execution<T> {
    pub nat_to_state: spec_fn(nat) -> T,
}

impl<T> Execution<T> {

    pub open spec fn suffix(self, pos: nat) -> Self {
        Execution {
            nat_to_state: |i: nat| (self.nat_to_state)(i + pos),
        }
    }

}


#[verifier(reject_recursive_types(T))]
pub struct TempPred<T> {
    pub pred: spec_fn(Execution<T>) -> bool,
}

impl<T> TempPred<T> {

    pub open spec fn new(pred: spec_fn(Execution<T>) -> bool) -> Self {
        TempPred {
            pred: pred,
        }
    }

    pub open spec fn satisfied_by(self, execution: Execution<T>) -> bool {
        (self.pred)(execution)
    }

    pub open spec fn implies(self, other: Self) -> Self {
        TempPred::new(|ex: Execution<T>| self.satisfied_by(ex) ==> other.satisfied_by(ex))
    }

    pub open spec fn leads_to(self, other: Self) -> Self {
        always(self.implies(eventually(other)))
    }

    pub open spec fn entails(self, other: Self) -> bool {
        valid(self.implies(other))
    }

}


pub open spec fn always<T>(temp_pred: TempPred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| forall |i: nat| #[trigger] temp_pred.satisfied_by(ex.suffix(i)))
}

pub open spec fn eventually<T>(temp_pred: TempPred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| exists |i: nat| #[trigger] temp_pred.satisfied_by(ex.suffix(i)))
}

pub open spec fn tla_forall<T, A>(a_to_temp_pred: spec_fn(A) -> TempPred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| forall |a: A| #[trigger] a_to_temp_pred(a).satisfied_by(ex))
}

pub open spec fn valid<T>(temp_pred: TempPred<T>) -> bool {
    forall |ex: Execution<T>| temp_pred.satisfied_by(ex)
}


// File: rules.rs
	#[verifier::external_body]
proof fn implies_apply<T>(ex: Execution<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        p.implies(q).satisfied_by(ex),
        p.satisfied_by(ex),
    ensures q.satisfied_by(ex),
	{
		unimplemented!()
	}

	#[verifier::external_body]
proof fn always_propagate_forwards<T>(ex: Execution<T>, p: TempPred<T>, i: nat)
    requires always(p).satisfied_by(ex),
    ensures always(p).satisfied_by(ex.suffix(i)),
	{
		unimplemented!()
	}

	#[verifier::external_body]
proof fn eventually_proved_by_witness<T>(ex: Execution<T>, p: TempPred<T>, witness_idx: nat)
    requires p.satisfied_by(ex.suffix(witness_idx)),
    ensures eventually(p).satisfied_by(ex)
	{
		unimplemented!()
	}

spec fn eventually_choose_witness<T>(ex: Execution<T>, p: TempPred<T>) -> nat
    recommends exists |i| p.satisfied_by(#[trigger] ex.suffix(i)),
{
    let witness = choose |i| p.satisfied_by(#[trigger] ex.suffix(i));
    witness
}

	#[verifier::external_body]
pub proof fn execution_equality<T>(ex1: Execution<T>, ex2: Execution<T>)
    requires forall |i: nat| #[trigger] (ex1.nat_to_state)(i) == (ex2.nat_to_state)(i),
    ensures ex1 == ex2,
	{
		unimplemented!()
	}

pub proof fn leads_to_always_tla_forall<T, A>(spec: TempPred<T>, p: TempPred<T>, a_to_p: spec_fn(A)->TempPred<T>, domain: Set<A>)
    requires
        forall |a: A| spec.entails(p.leads_to(always(#[trigger] a_to_p(a)))),
        domain.finite(),
        domain.len() > 0,
        forall |a: A| #[trigger] domain.contains(a),
    ensures spec.entails(p.leads_to(always(tla_forall(a_to_p)))),
{
    assert forall |ex| #[trigger] spec.satisfied_by(ex) implies p.leads_to(always(tla_forall(a_to_p))).satisfied_by(ex) by {
        assert forall |i| #[trigger] p.satisfied_by(ex.suffix(i)) implies eventually(always(tla_forall(a_to_p))).satisfied_by(ex.suffix(i)) by {
            assert forall |a: A| p.leads_to(always(#[trigger] a_to_p(a))).satisfied_by(ex) by {
                implies_apply::<T>(ex, spec, p.leads_to(always(a_to_p(a))));
            }
            assert forall |a: A| eventually(always(#[trigger] a_to_p(a))).satisfied_by(ex.suffix(i)) by {
                implies_apply::<T>(ex.suffix(i), p, eventually(always(a_to_p(a))));
            }

            let a_to_witness = Map::new(|a: A| domain.contains(a), |a: A| {
                let wit = eventually_choose_witness::<T>(ex.suffix(i), always(a_to_p(a)));
                wit
            });
            assert(a_to_witness.dom() =~= domain);
            assert(a_to_witness.dom() == domain);
            assert(a_to_witness.dom().finite());
            assert(a_to_witness.dom().len() > 0);
            let r = |a1: nat, a2: nat| a1 <= a2;
            let values = a_to_witness.values();
            lemma_values_finite(a_to_witness);
            assert_by(
                values.len() > 0, {
                let x = a_to_witness.dom().choose();
                assert(a_to_witness.contains_key(x));
                assert(a_to_witness.contains_value(a_to_witness[x]));
                assert(values.contains(a_to_witness[x]));
            });
            let max_witness = values.find_unique_maximal(r);
            values.find_unique_maximal_ensures(r);
            values.lemma_maximal_equivalent_greatest(r, max_witness);

            assert forall |a: A| always(#[trigger] a_to_p(a)).satisfied_by(ex.suffix(i).suffix(max_witness)) by {
                assert(domain.contains(a));
                assert(vstd::relations::is_greatest(r, max_witness, values));
                let witness = a_to_witness[a];
                assert(r(witness, max_witness));
                assert(max_witness >= witness);
                always_propagate_forwards::<T>(ex.suffix(i).suffix(witness), a_to_p(a), (max_witness - witness) as nat);
                execution_equality::<T>(ex.suffix(i).suffix(max_witness), ex.suffix(i).suffix(witness).suffix((max_witness - witness) as nat));
            }
            eventually_proved_by_witness(ex.suffix(i), always(tla_forall(a_to_p)), max_witness);
        };
    };
}


}
