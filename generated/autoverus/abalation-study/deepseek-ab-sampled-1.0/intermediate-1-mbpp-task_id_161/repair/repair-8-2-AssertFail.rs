
#[allow(unused_imports)]
use vstd::prelude::*;
fn main() {}

verus! {
spec fn seq_to_set_rec<A>(seq: Seq<A>) -> Set<A>
    decreases seq.len()
{
    if seq.len() == 0 {
        Set::empty()
    } else {
        seq_to_set_rec(seq.drop_last()).insert(seq.last())
    }
}

proof fn seq_to_set_rec_contains<A>(seq: Seq<A>)
    ensures forall |a| #[trigger] seq.contains(a) <==> seq_to_set_rec(seq).contains(a)
    decreases seq.len()
{
    if seq.len() > 0 {
        assert(forall |a| #[trigger] seq.drop_last().contains(a) <==> seq_to_set_rec(seq.drop_last()).contains(a)) by {
            seq_to_set_rec_contains(seq.drop_last());
        }

        assert(seq.ext_equal(seq.drop_last().push(seq.last())));
        assert forall |a| #[trigger] seq.contains(a) <==> seq_to_set_rec(seq).contains(a) by {
            if !seq.drop_last().contains(a) {
                if a == seq.last() {
                    assert(seq.contains(a));
                    assert(seq_to_set_rec(seq).contains(a));
                } else {
                    assert(!seq_to_set_rec(seq).contains(a));
                }
            }
        }
    }
}

proof fn lemma_seq_push_to_set_insert<T>(s: Seq<T>, val: T)
    ensures
        s.push(val).to_set() === s.to_set().insert(val),
{
    seq_to_set_rec_contains(s.push(val));
    seq_to_set_rec_contains(s);
    assert(s.push(val).to_set() === seq_to_set_rec(s.push(val)));
    assert(s.push(val).to_set() === seq_to_set_rec(s).insert(val));
}

proof fn lemma_vec_remove_contains<T>(vec: Seq<T>, i: int)
    requires
        0 <= i < vec.len(),
    ensures
        forall |k: int| 0 <= k < i ==> #[trigger] vec[k] == vec.remove(i)[k],
        forall |k: int| i < k  < vec.len() ==> #[trigger] vec[k] ==  vec.remove(i)[k-1],
{
}

proof fn lemma_vec_push_contains<T>(vec: Seq<T>, i: T, l: usize)
    requires
        l == vec.len(),
    ensures
        forall |k: int| 0 <= k < vec.len() ==> #[trigger] vec[k] == vec.push(i)[k],
        vec.push(i).index(l as int) == i,
{
}

#[verifier::loop_isolation(false)]
fn contains(str: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
{
    let mut i = 0;
    while i < str.len() {
        if (str[i] == key) {
            return true;
        }
        i += 1;
    }
    false
}

fn remove_elements(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        forall|i: int|
            0 <= i < result.len() ==> (arr1@.contains(#[trigger] result[i]) && !arr2@.contains(
                #[trigger] result[i],
            )),
        forall|i: int|
            0 <= i < arr1.len() ==> (arr2@.contains(#[trigger] arr1[i]) || result@.contains(
                #[trigger] arr1[i],
            )),
{
    let mut output_str = Vec::new();
    let mut index: usize = 0;

    while index < arr1.len()
        invariant
            forall |k: int| 0 <= k < output_str.len() ==> !arr2@.contains(output_str[k]),
            0 <= index <= arr1.len(),
            output_str.len() <= index,
    {
        if (!contains(arr2, arr1[index])) {
            let val = arr1[index];
            output_str.push(val);
            proof {
                lemma_vec_push(output_str @, arr1[( index ) as int], output_str.len());
                lemma_seq_push_to_set_insert(output_str @.into_seq(), val);
                lemma_seq_push_to_set_insert(arr1 @.into_seq().subrange(0, index as int + 1), val);
            }
        }
        index += 1;
    }

    proof {
        assert(forall |i: int| 0 <= i < arr1.len() ==> (arr2@.contains(arr1[i]) || output_str@.contains(arr1[i])))
            by {
                induction_on i;
                case i = 0 {
                    base case;
                }
                case i = k + 1 {
                    induction hypothesis: for all i <= k, arr2@.contains(arr1[i]) || output_str@.contains(arr1[i]);
                    step:
                        assertion holds for i = k + 1;
                }
            }
        lemma_seq_subrange_all(arr1 @.into_seq());
    }

    output_str
}

proof fn lemma_seq_subrange_ascend<T>(v: Seq<T>, i: int, j: int)
    requires
        0 <= i < j <= v.len(),
    ensures
        v.subrange(i as int, j as int).drop_last() == v.subrange(i as int, j as int - 1 ),
{
    assert(v.subrange(i as int, j as int).drop_last() =~= v.subrange(i as int, j as int - 1));
}

proof fn lemma_seq_subrange_all<T>(v: Seq<T>)
    ensures
        v == v.subrange(0, v.len() as int),
{
    assert(v =~= v.subrange(0, v.len() as int));
}
}


//         assert(forall |i: int| 0 <= i < arr1.len() ==> (arr2@.contains(arr1[i]) || output_str@.contains(arr1[i])));
//   assertion failed: forall |i: int| 0 <= i < arr1.len() ==> (arr2@.contains(arr1[i]) || output_str@.contains(arr1[i]))

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False