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
