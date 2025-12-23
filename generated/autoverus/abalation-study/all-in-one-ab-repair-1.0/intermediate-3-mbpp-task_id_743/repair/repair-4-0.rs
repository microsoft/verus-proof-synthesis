
use vstd::prelude::*;
fn main() {}

verus! {
    spec fn sorted_between(a: Seq<u32>, from: int, to: int) -> bool {
        forall |i: int, j:int|  from <= i < j < to ==> a[i] <= a[j]
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
            proof {
                assert(exists|r: Seq<int>| is_reorder_of(r, nums@, nums@));
            } 
            return;
        }
        for i in 1..n
            invariant
                n == nums.len(),
                sorted_between(nums@, 0, i as int),
                exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@),
        {
            let mut j = i;
            while j != 0
                invariant
                    0 <= j <= i,
                    forall|x: int, y: int| 0 <= x <= y <= i ==> x != j && y != j ==> nums[x] <= nums[y],
                    sorted_between(nums@, j as int, i + 1),
                    exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@),
            {
                if nums[j - 1] > nums[j] {
                    proof {
                        let r1 = choose|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@);
                        let r2 = r1.update(j-1, r1[j as int]).update(j as int, r1[j-1]);
                        assert(is_reorder_of(r2, nums@.update(j-1, nums@[j as int]).update(j as int, nums@[j-1]), old(nums)@));
                    }
                    let temp = nums[j - 1];
                    nums.set(j - 1, nums[j]);
                    nums.set(j, temp);
                }
                j -= 1;
                proof {
                    assert(exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@));
                }
            }
        }
    }

    #[verifier::loop_isolation(false)]
    spec fn rotation_split(len: usize, n: usize) -> int {
        len - (n % len)
    }

    fn rotate_right(list: &Vec<u32>, n: usize) -> (new_list: Vec<u32>)
        requires
            list.len() > 0,
        ensures
            new_list.len() == list.len(),
            new_list@ == list@.subrange(rotation_split(list.len(), n) as int, list@.len() as int).add(
                list@.subrange(0, rotation_split(list.len(), n) as int)
            ),
    {
        let rotation = n % list.len();
        let split_index = list.len() - rotation;
        let mut new_list = Vec::with_capacity(list.len());
        let mut index = split_index;
        
        while index < list.len()
            invariant
                index <= list.len(),
                new_list.len() == index - split_index,
                new_list@ == list@.subrange(split_index as int, index as int),
        {
            new_list.push(list[index]);
            index += 1;
        }
        
        index = 0;
        
        while index < split_index
            invariant
                index <= split_index,
                new_list.len() == list.len() - split_index + index,
                new_list@ == list@.subrange(split_index as int, list.len() as int).add(list@.subrange(0, index as int)),
        {
            new_list.push(list[index]);
            index += 1;
        }
        
        new_list
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp4sdobyx6`)
// 

// Compilation Error: False, Verified: 1, Errors: 5, Verus Errors: 11
// Safe: False