use vstd::multiset::Multiset;
use vstd::prelude::*;
fn main() {}

verus! {
    spec fn sorted_between(a: Seq<u32>, from: int, to: int) -> bool {
        forall |i: int, j:int|  from <= i < j < to ==> a[i] <= a[j]
    }

    spec fn multiset_from_seq<T>(input: Seq<T>) -> Multiset<T>
    decreases
        input.len()
    {
        if input.len() == 0 {
            Multiset::empty()
        } else {
            multiset_from_seq(input.drop_last()).insert(input.last())
        }
    }

    proof fn proof_lemma_multiset_count<T>(input: Seq<T>, i: int)
    requires
        0 <= i < input.len(),
    ensures
        multiset_from_seq(input).count(input[i]) > 0,
    decreases
        input.len(),
    {
        let input_no_last = input.drop_last();
        let c = multiset_from_seq(input).count(input[i]);
        if i < (input.len() - 1) {
            proof_lemma_multiset_count(input.drop_last(), i);
            assert(c >= multiset_from_seq(input_no_last).count(input[i]));
        } else {
            assert(c == multiset_from_seq(input_no_last).count(input[i]) + 1);
        }
    }

    proof fn proof_lemma_multiset_insert<T>(input: Seq<T>, i: int, v: T)
    requires
        0 <= i < input.len(),
    ensures
        multiset_from_seq(input.update(i, v)).ext_equal(multiset_from_seq(input).remove(input[i]).insert(v)),
    decreases
        input.len(),
    {
        let ret1 = multiset_from_seq(input.update(i, v));
        let ret2 = multiset_from_seq(input);
        let input_no_last = input.drop_last();
        let ret1_no_last = multiset_from_seq(input_no_last.update(i, v));
        let ret2_no_last = multiset_from_seq(input_no_last);
        let last = input.last();
        if i < input.len() - 1 {
            proof_lemma_multiset_insert(input_no_last, i, v);
            assert(ret2 === ret2_no_last.insert(last));
            let input_update_no_last = input.update(i, v).drop_last();
            assert(input_update_no_last.ext_equal(input_no_last.update(i, v)));
            assert(ret1_no_last === ret2_no_last.remove(input[i]).insert(v));
            assert(ret1 === ret1_no_last.insert(last));
            assert(ret1.ext_equal(ret2_no_last.remove(input[i]).insert(v).insert(last)));
            let ret2_remove_insert = ret2.remove(input[i]).insert(v);
            assert(ret1.ext_equal(ret2_remove_insert)) by {
                assert forall |w: T| ret1.count(w) == ret2_remove_insert.count(w)
                by {
                    let input_op: int = if (input[i] === w) {1} else {0};
                    let v_op: int = if (v === w) {1} else {0};
                    let last_op: int = if last === w {1}else {0};
                    assert(ret2.remove(input[i]).count(w) + v_op == ret2_remove_insert.count(w));
                    assert(ret2.count(input[i]) > 0 ) by {
                        proof_lemma_multiset_count(input, i);
                    }
                    assert(ret2.count(w) - input_op == ret2.remove(input[i]).count(w));
                    assert(ret2.count(w) == ret2_no_last.count(w) + last_op);
                    assert(ret2_no_last.count(input[i]) > 0) by {
                        proof_lemma_multiset_count(input_no_last, i);
                    }
                    assert(ret2_no_last.remove(input[i]).count(w) == ret2_no_last.count(w) - input_op);
                    assert(ret2_no_last.remove(input[i]).insert(v).count(w) == ret2_no_last.remove(input[i]).count(w) + v_op);
                    assert(ret1.count(w) == ret2_no_last.remove(input[i]).insert(v).count(w) + last_op);
                }
            }
        } else {
            assert(input.update(i, v).drop_last().ext_equal(input_no_last));
            assert(ret1 === ret2_no_last.insert(v));
            assert(ret2 === ret2_no_last.insert(input[i]));
        }
    }

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
        invariant
            n == nums@.len(),
            sorted_between(nums@, 0, i as int),
            multiset_from_seq(old(nums)@).ext_equal(multiset_from_seq(nums@))
        {
            let mut j = i;
            while j > 0
            invariant
                n == nums@.len(),
                i < n,
                0 <= j <= i,
                forall|u: int,v: int| 0 <= u < (j as int) < v < (i as int) +1 ==> nums@[u] <= nums@[v],
                sorted_between(nums@, 0, j as int),
                sorted_between(nums@, j as int, i as int + 1),
                multiset_from_seq(old(nums)@).ext_equal(multiset_from_seq(nums@)),
            {
                if nums[j-1] > nums[j] {
                    let temp = nums[j-1];
                    proof {
                        proof_lemma_multiset_insert(nums@, j as int - 1, nums@[j as int]);
                        proof_lemma_multiset_count(nums@, j as int - 1);
                    }
                    nums.set(j-1, nums[j]);
                    proof {
                        proof_lemma_multiset_insert(nums@, j as int, temp);
                        proof_lemma_multiset_count(nums@, j as int);
                    }
                    nums.set(j, temp);
                }
                assert(nums@[j as int-1] <= nums@[j as int]);
                j = j - 1;
                proof {
                    assert forall |u: int, v:int|
                        j as int <= u < v < i as int + 1
                    implies
                        nums@[u] <= nums@[v]
                    by{
                        if u != j {
                            assert(nums@[u] <= nums@[v]);
                        } else {
                            assert(u == j);
                            assert(nums@[u] <= nums@[j as int+1]);
                            assert(nums@[j as int+1] <= nums@[v]);
                        }
                    }

                }
            }
        }
    }
}
