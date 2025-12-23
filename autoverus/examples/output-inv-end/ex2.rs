use vstd::multiset::Multiset;
use vstd::prelude::*;
fn main() {}

verus! {

spec fn sorted_between(a: Seq<u32>, from: int, to: int) -> bool {

    forall|i: int, j:int| from <= i < j < to ==> a[i] <= a[j]

}

spec fn multiset_from_seq<T>(input: Seq<T>) -> Multiset<T>

    decreases input.len()

{

    if input.len() == 0 {

        Multiset::empty()

    } else {

        multiset_from_seq(input.drop_last()).insert(input.last())

    }

}

proof fn update_seq_multiset<T>(s: Seq<T>, i: int, v: T)
    requires
        0 <= i < s.len(),
    ensures
        multiset_from_seq(s).contains(s[i]),
        multiset_from_seq(s.update(i, v)) =~= multiset_from_seq(s).remove(s[i]).insert(v),
    decreases
        s.len(),
{
    if i == s.len() - 1 {
        assert(s.update(i, v) =~= s.drop_last().push(v));
        assert(multiset_from_seq(s) == multiset_from_seq(s.drop_last()).insert(s.last()));
        assert(s.drop_last().push(v).drop_last() =~= s.drop_last());
    } else if s.len() != 0 {
        update_seq_multiset(s.drop_last(), i, v);
        assert(s.drop_last().update(i, v) =~= s.update(i, v).drop_last());
    }
}


#[verifier::loop_isolation(false)]

fn test1(nums: &mut Vec<u32>)
    ensures
        sorted_between(nums@, 0, nums@.len() as int),
        multiset_from_seq(old(nums)@) === multiset_from_seq(nums@)
{

    let n = nums.len();

    if n == 0 {
        return;
    }

    for i in 1..n
        invariant
            n == nums.len(),
            sorted_between(nums@, 0, i as int),
            multiset_from_seq(old(nums)@) === multiset_from_seq(nums@)
    {
        let mut j = i;

        while j != 0
            invariant
                j <= i,
                i < n,
                n == nums.len(),
                forall|x: int, y: int| 0 <= x <= y <= i ==> x != j && y != j ==> nums[x] <= nums[y],
                j >= 0, // Fixed by AI
                sorted_between(nums@, j as int, i + 1),
                multiset_from_seq(old(nums)@) === multiset_from_seq(nums@)
        {

            if nums[j - 1] > nums[j] {

                let temp = nums[j - 1];

                proof {
                    update_seq_multiset(nums@, j-1, nums[j as int])
                }
                nums.set(j - 1, nums[j]);

                assert(multiset_from_seq(old(nums)@) == multiset_from_seq(nums@).remove(nums[j as int]).insert(temp));

                proof{
                    update_seq_multiset(nums@, j as int, temp)
                }
                nums.set(j, temp);
            }

            j -= 1;

        }

    }

}
}
