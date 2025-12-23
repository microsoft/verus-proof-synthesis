
use vstd::prelude::*;
fn main() {}
verus! {
/*
 This lemma is often useful before a vector-remove call, and it can be useful to prove what element is contained in a vector.
 The parameters to this lemma function should match the executable code after it.
 Do NOT pass `old(..)' to this lemma as parameter.
 Example usage:
    proof{
	lemma_vec_remove(vec@, index);
    }
    vec.remove(index); 
 */
proof fn lemma_vec_remove<T>(vec: Seq<T>, i: int)
    requires
        0 <= i < vec.len(),
    ensures
        forall |k: int| 0 <= k < i ==> #[trigger] vec[k] == vec.remove(i)[k],
        forall |k: int| i < k  < vec.len() ==> #[trigger] vec[k] ==  vec.remove(i)[k-1],
{
    
}

/*
 This lemma is often useful before a vector-push call, and it can be useful to prove what element is contained in a vector.
 Example usage:
    proof{
	lemma_vec_push(vec@, value, vec.len());
    }
    vec.push(value); 
 */
proof fn lemma_vec_push<T>(vec: Seq<T>, i: T, l: usize)
    requires
        l == vec.len(),
    ensures
        forall |k: int| 0 <= k < vec.len() ==> #[trigger] vec[k] == vec.push(i)[k],
        vec.push(i).index(l as int) == i,
{
}

#[verifier::loop_isolation(false)]

pub fn remove_all_greater(v: Vec<i32>, e: i32) -> (result: Vec<i32>)
    requires
        forall|k1: int, k2: int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2],
    ensures
        forall|k: int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]),
        forall|k: int| 0 <= k < v.len() && v[k] <= e ==> result@.contains(v[k]),
{
    let mut i: usize = 0;
    let vlen = v.len();
    let mut result: Vec<i32> = vec![];
    while (i < v.len())
        invariant
            forall|k: int| 0 <= k < i && v[k] <= e ==> result@.contains(v[k]),
            forall|k: int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]),
            i <= v.len(),
            result@.len() <= i,
            forall|k1: int, k2: int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2],
            v.len() == vlen,
            result.len() <= v.len(),
    {
        if (v[i] <= e) {
            proof {
                lemma_vec_push(result@, v[( i ) as int], result.len());
            }
            result.push(v[i]);
        }
        i = i + 1;
        proof {
            assert(forall|k: int| 0 <= k < i && v[k] <= e ==> result@.contains(v[k]));
        }
    }
    result
}

} // verus!



//             assert(forall|k: int| 0 <= k < i && v[k] <= e ==> result@.contains(v[k]));
//   assertion failed: forall|k: int| 0 <= k < i && v[k] <= e ==> result@.contains(v[k])

// Compilation Error: False, Verified: 3, Errors: 0, Verus Errors: 0
// Safe: True