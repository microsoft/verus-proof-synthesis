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


    #[verifier::loop_isolation(false)]

    fn bubble_sort(nums: &mut Vec<u32>)
        ensures
            sorted_between(nums@, 0, nums@.len() as int),
            multiset_from_seq(old(nums)@) === multiset_from_seq(nums@)
    {

        let n = nums.len();

        if n == 0 {
            return;
        }

        for i in 1..n
        {
            let mut j = i;

            while j != 0
            {
                if nums[j - 1] > nums[j] {
                    let temp = nums[j - 1];
                    nums.set(j - 1, nums[j]);
                    nums.set(j, temp);
                }
                j -= 1;
            }
        }

    }
}
