
use vstd::prelude::*;

fn main() {}

verus! {
/*
 This lemma is often useful to put right after a loop that has a loop invariant involving Seq::subrange(0, i), with i being the loop index.

 Example usage:
    while ( k < s.len() )
      invariant
          ...
          k <= s.len(),
          ...s@.subrange(0, k as int)...,
          ...
    {
       ...
       k = k + 1;
    }
    proof{
     	lemma_seq_subrange_all(s@);
    }
 */

proof fn lemma_seq_subrange_all<T>(v: Seq<T>)
    ensures
        v == v.subrange(0, v.len() as int),
{
    assert(v =~= v.subrange(0, v.len() as int));
}

/*
 This lemma is often useful to put near the end of a loop body that has a loop invariant involving Seq::subrange(j, k), with k being the loop index. It will help prove the property of range j..k+1 of a Sequence based on the property held for range j..k of a Sequence.
 
 Example usage:
    while ( k < s.len() )
      invariant
          ...
          k <= s.len(),
          ...s@.subrange(j, k as int)...,
          ...
    {
       ...
       proof{
       	  lemma_seq_subrange_ascend(s@, j, k+1);
       }
       k = k + 1;
    }

 */

proof fn lemma_seq_subrange_ascend<T>(v: Seq<T>, i: int, j: int)
    requires
        0 <= i < j <= v.len(),
    ensures
        v.subrange(i as int, j as int).drop_last() == v.subrange(i as int, j-1),
{
    reveal(Seq::drop_last);  // Revealing drop_last if it's used in an assertion for completeness
    assert(v.subrange(i as int, j as int).drop_last() =~= v.subrange(i as int, j-1));
}

proof fn lemma_seq_subrange_all<T>(v: Seq<T>)
    ensures
        v == v.subrange(0, v.len() as int),
{
    assert(v =~= v.subrange(0, v.len() as int));
}

proof fn seq_filter_push_eq<T>(s: Seq<T>, f: FnSpec(T) -> bool, x: T)
    requires
        f(x) == true,
    ensures
        s.push(x).filter(f) =~= s.filter(f).push(x)
{
    reveal(Seq::push);  // Revealing Seq::push
    reveal(Seq::filter);  // Revealing Seq::filter
    assert(s.push(x).filter(f) =~= s.filter(f).push(x));
}

proof fn seq_filter_not_contains<T>(s: Seq<T>, f: FnSpec(T) -> bool, x: T)
    requires
        f(x) == false,
    ensures
        s.push(x).filter(f) =~= s.filter(f)
{
    reveal(Seq::push);  // Revealing Seq::push
    reveal(Seq::filter);  // Revealing Seq::filter
    assert(s.push(x).filter(f) =~= s.filter(f));
}

fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
{
    proof {
        reveal(Seq::filter);  // Revealing Seq::filter for the function context
    }

    let mut even_numbers: Vec<u32> = Vec::new();
    let mut index = 0;

    proof {
        assert(even_numbers@ == arr@.subrange(0, 0).filter(|x: u32| x % 2 == 0));
    }

    while index < arr.len()
        invariant
            index <= arr.len(),
            forall |k: int| 0 <= k < arr.len() ==> arr[k] == arr[k],
            even_numbers.len() == even_numbers.len(),
            even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0),
    {
        if (arr[index] % 2 == 0) {
            even_numbers.push(arr[index]);
            proof {
                lemma_seq_subrange_ascend(arr@, 0, index as int + 1);
                let sub_filtered = arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0);
                seq_filter_push_eq(sub_filtered, |x: u32| x % 2 == 0, arr@[index as int]);
                assert(arr@.subrange(0, index as int + 1).filter(|x: u32| x % 2 == 0) =~= sub_filtered.push(arr@[index as int]));
            }
        } else {
            proof {
                let sub_filtered = arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0);
                seq_filter_not_contains(sub_filtered, |x: u32| x % 2 == 0, arr@[index as int]);
                assert(arr@.subrange(0, index as int + 1).filter(|x: u32| x % 2 == 0) =~= sub_filtered);
            }
        }
        index += 1;
        proof {
            assert(even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0));
        }
    }

    proof {
        lemma_seq_subrange_all(arr@);
    }

    even_numbers
}
}


//             assert(even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0));
//   assertion failed: even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0)

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False