use vstd::prelude::*;
fn main() {}

verus! {

proof fn lemma_sorted_between_single_element(a: Seq<u32>, i: int)
    requires
        0 <= i < a.len() as int,
    ensures
        sorted_between(a, i, i + 1),
{
    assert(sorted_between(a, i, i + 1));
    assert(forall |x: int, y:int| i <= x < y < (i + 1) ==> a[x] <= a[y]);
}

proof fn lemma_sorted_between_transitive(a: Seq<u32>, i: int, j: int, k: int)
    requires
        sorted_between(a, i, k),
        i <= j,
        j <= k,
    ensures
        sorted_between(a, i, j),
        sorted_between(a, j, k),
{
    assert(sorted_between(a, i, k));
    assert(forall |x: int, y:int| i <= x < y < j ==> a[x] <= a[y]);
    assert(forall |x: int, y:int| j <= x < y < k ==> a[x] <= a[y]);
}

spec fn sorted_between(a: Seq<u32>, from: int, to: int) -> bool {
    forall |i: int, j:int| from <= i < j < to ==> a[i] <= a[j]
}

spec fn is_reorder_of<T>(r: Seq<int>, p: Seq<T>, s: Seq<T>) -> bool {
    &&& r.len() == s.len()
    &&& forall|i: int| 0 <= i < r.len() ==> 0 <= #[trigger] r[i] < r.len()
    &&& forall|i: int, j: int| 0 <= i < j < r.len() ==> r[i] != r[j]
    &&& p =~= r.map_values(|i: int| s[i])
}

fn test1(nums: &mut Vec<u32>)
    ensures
        sorted_between(nums@, 0, nums@.len() as int),
        exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@),
{
    let n = nums.len();
    if n == 0 {
        return;
    }
    proof {
        let q = Seq::new(nums@.len(), |i: int| i); // Fixed by AI
    }
    for i in 1..n
    invariant
        1 <= i <= n,
        sorted_between(nums@, 0, i as int),
        exists|r: Seq<int>| is_reorder_of(r, nums@.take(i as int), old(nums)@),
    {
        let mut j = i;
        while j > 0
        invariant
            0 < j <= i,
            sorted_between(nums@, 0, j as int),
            sorted_between(nums@, j as int, i as int + 1),
            exists|r: Seq<int>| is_reorder_of(r, nums@.take(i as int), old(nums)@),
        {
            if nums[j - 1] > nums[j] {
                let temp = nums[j - 1];
                nums.set(j - 1, nums[j]);
                nums.set(j, temp);
                proof {
                    lemma_sorted_between_single_element(nums@, j as int - 1);
                }
            }
            proof {
                lemma_sorted_between_transitive(nums@, 0, j as int, i as int + 1);
            }
            j -= 1;
        }
    }
}
}
